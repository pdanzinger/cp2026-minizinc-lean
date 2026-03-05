from __future__ import annotations

import json
import os
import hashlib
import shutil
import subprocess
import tempfile
import time
import math
from collections import deque
import signal
from dataclasses import asdict, dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, Optional
import psutil
import numpy as np

import structlog
import submitit

from scipy.stats import wilcoxon

from concurrent.futures import ThreadPoolExecutor, as_completed
from .helpers_slurm import configure_executor, create_slurm_tmp_folder

log = structlog.get_logger()


class SolveStatus(str, Enum):
    ERROR = "ERROR"
    TIMEOUT = "TIMEOUT"
    FEASIBLE = "FEASIBLE"
    OPTIMAL = "OPTIMAL"


class ObjectiveSense(str, Enum):
    MIN = "min"
    MAX = "max"

class ScoreMode(str, Enum):
    # MiniZinc Challenge-style pairwise scoring with fixed time-fraction tie breaks
    # (timeUsed fractions, i.e. temperature=1). Ignores temperature parameters.
    MINIZINC = "minizinc"
    # Custom soft variant: interpolate time/objective comparisons using
    # temperature parameters (keeps existing behavior/default).
    MINIZINC_SOFT = "minizinc_soft"
    # MiniZinc Challenge "area" scoring based on objective traces (integral over time).
    MINIZINC_AREA = "minizinc_area"

    @classmethod
    def _missing_(cls, value: object) -> "ScoreMode | None":
        if isinstance(value, str):
            v = value.strip().lower()
            if v == "soft":
                return cls.MINIZINC_SOFT
            if v == "hard":
                return cls.MINIZINC
        return None


@dataclass(frozen=True)
class RunResult:
    instance: str
    run_id: int
    status: SolveStatus
    objective_value: Optional[float]
    compile_time_s: float
    solve_time_s: float
    error: bool
    error_message: Optional[str]
    minizinc_exit_code: Optional[int]
    # List of (time_s_since_start, objective_value) pairs for strictly improving objectives.
    # Empty for satisfaction problems and unsolved/error cases.
    objective_trace: list[tuple[float, float]] = field(default_factory=list)
    # Time to first printed solution (if any), relative to solve start.
    # For satisfaction problems we stop at the first solution, so this is also the solve time.
    first_solution_time_s: Optional[float] = None
    # Time when objective_value was reached (if known), relative to solve start.
    objective_value_time_s: Optional[float] = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "instance": self.instance,
            "run_id": self.run_id,
            "status": self.status.value,
            "objective_value": self.objective_value,
            "objective_trace": [[float(t), float(v)] for (t, v) in self.objective_trace],
            "first_solution_time_s": self.first_solution_time_s,
            "objective_value_time_s": self.objective_value_time_s,
            "compile_time_s": self.compile_time_s,
            "solve_time_s": self.solve_time_s,
            "error": self.error,
            "error_message": self.error_message,
            "minizinc_exit_code": self.minizinc_exit_code,
        }

    @staticmethod
    def from_dict(d: dict[str, Any]) -> "RunResult":
        trace: list[tuple[float, float]] = []
        raw_trace = d.get("objective_trace") or []
        if isinstance(raw_trace, list):
            for item in raw_trace:
                if isinstance(item, (list, tuple)) and len(item) == 2:
                    try:
                        trace.append((float(item[0]), float(item[1])))
                    except (TypeError, ValueError):
                        continue
                elif isinstance(item, dict):
                    try:
                        trace.append((float(item.get("t_s")), float(item.get("objective_value"))))
                    except (TypeError, ValueError):
                        continue
        return RunResult(
            instance=str(d["instance"]),
            run_id=int(d["run_id"]),
            status=SolveStatus(str(d["status"])),
            objective_value=(None if d.get("objective_value") is None else float(d["objective_value"])),
            objective_trace=trace,
            first_solution_time_s=(
                None if d.get("first_solution_time_s") is None else float(d["first_solution_time_s"])
            ),
            objective_value_time_s=(
                None if d.get("objective_value_time_s") is None else float(d["objective_value_time_s"])
            ),
            compile_time_s=float(d["compile_time_s"]),
            solve_time_s=float(d["solve_time_s"]),
            error=bool(d["error"]),
            error_message=(None if d.get("error_message") is None else str(d["error_message"])),
            minizinc_exit_code=(None if d.get("minizinc_exit_code") is None else int(d["minizinc_exit_code"])),
        )


@dataclass(frozen=True)
class BenchmarkResult:
    solver: str
    timeout_s: float
    runs_per_instance: int
    objective_sense: ObjectiveSense
    instances: list[str]
    runs_by_instance: dict[str, list[RunResult]]

    def to_dict(self) -> dict[str, Any]:
        return {
            "solver": self.solver,
            "timeout_s": self.timeout_s,
            "runs_per_instance": self.runs_per_instance,
            "objective_sense": self.objective_sense.value,
            "instances": list(self.instances),
            "runs_by_instance": {
                inst: [r.to_dict() for r in self.runs_by_instance[inst]] for inst in self.instances
            },
        }

    @staticmethod
    def from_dict(d: dict[str, Any]) -> "BenchmarkResult":
        instances = [str(x) for x in d["instances"]]
        runs_by_instance = {
            str(inst): [RunResult.from_dict(r) for r in d["runs_by_instance"][inst]] for inst in instances
        }
        return BenchmarkResult(
            solver=str(d["solver"]),
            timeout_s=float(d["timeout_s"]),
            runs_per_instance=int(d["runs_per_instance"]),
            objective_sense=ObjectiveSense(str(d.get("objective_sense", ObjectiveSense.MIN.value))),
            instances=instances,
            runs_by_instance=runs_by_instance,
        )


@dataclass(frozen=True)
class RunComparison:
    incumbent_score: float
    new_score: float
    reason: str


@dataclass(frozen=True)
class BenchmarkComparison:
    score_mode: str
    incumbent_score: float
    new_score: float
    total_compared: int
    incumbent_avg_score: float
    new_avg_score: float
    per_instance: dict[str, dict[str, float]]

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

@dataclass(frozen=True)
class WilcoxonResult:
    p_value: float
    n_instances: int
    n_nonzero: int

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def compute_result_geomean_opt_time(
    solver_benchmarks: list[BenchmarkResult],
) -> list[float | None]:
    if not solver_benchmarks:
        return []

    keyed_runs_by_solver: list[dict[tuple[str, int], RunResult]] = []
    for solver_benchmark in solver_benchmarks:
        solver_keyed_runs: dict[tuple[str, int], RunResult] = {}
        for inst in solver_benchmark.instances:
            for run in solver_benchmark.runs_by_instance.get(inst, []):
                if run.status == SolveStatus.OPTIMAL:
                    solver_keyed_runs[(inst, run.run_id)] = run
        keyed_runs_by_solver.append(solver_keyed_runs)

    shared_instance_run_keys = set(keyed_runs_by_solver[0].keys())
    for solver_keyed_runs in keyed_runs_by_solver[1:]:
        shared_instance_run_keys &= set(solver_keyed_runs.keys())
    if not shared_instance_run_keys:
        return [None] * len(solver_benchmarks)

    ordered_instance_run_keys = sorted(shared_instance_run_keys)
    solver_geomeans: list[float | None] = []
    for solver_keyed_runs in keyed_runs_by_solver:
        values = np.asarray(
            [float(solver_keyed_runs[key].solve_time_s) for key in ordered_instance_run_keys],
            dtype=float,
        )
        values = values[np.isfinite(values)]
        values = values[values > 0.0]
        if values.size == 0:
            solver_geomeans.append(None)
            continue
        solver_geomeans.append(float(np.exp(np.mean(np.log(values)))))
    return solver_geomeans


def compute_geomean_objective(
    solver_benchmarks: list[BenchmarkResult],
) -> list[float | None]:
    if not solver_benchmarks:
        return []

    valid_statuses = {SolveStatus.OPTIMAL, SolveStatus.FEASIBLE}
    keyed_runs_by_solver: list[dict[tuple[str, int], RunResult]] = []
    for solver_benchmark in solver_benchmarks:
        solver_keyed_runs: dict[tuple[str, int], RunResult] = {}
        for inst in solver_benchmark.instances:
            for run in solver_benchmark.runs_by_instance.get(inst, []):
                if run.status in valid_statuses and run.objective_value is not None:
                    solver_keyed_runs[(inst, run.run_id)] = run
        keyed_runs_by_solver.append(solver_keyed_runs)

    shared_instance_run_keys = set(keyed_runs_by_solver[0].keys())
    for solver_keyed_runs in keyed_runs_by_solver[1:]:
        shared_instance_run_keys &= set(solver_keyed_runs.keys())
    if not shared_instance_run_keys:
        return [None] * len(solver_benchmarks)

    ordered_instance_run_keys = sorted(shared_instance_run_keys)
    solver_geomeans: list[float | None] = []
    for solver_keyed_runs in keyed_runs_by_solver:
        values = np.asarray(
            [float(solver_keyed_runs[key].objective_value) for key in ordered_instance_run_keys],
            dtype=float,
        )
        values = values[np.isfinite(values)]
        values = values[values > 0.0]
        if values.size == 0:
            solver_geomeans.append(None)
            continue
        solver_geomeans.append(float(np.exp(np.mean(np.log(values)))))
    return solver_geomeans


def _discover_dzn_files(dzn_files: Optional[list[Path]], dzn_dir: Optional[Path]) -> list[Path]:
    if dzn_files and dzn_dir:
        raise ValueError("Provide either dzn_files or dzn_dir, not both.")
    if dzn_files:
        files = [Path(p) for p in dzn_files]
        missing = [str(p) for p in files if not p.exists()]
        if missing:
            raise FileNotFoundError(f"Missing .dzn files: {missing}")
        return sorted(files)
    if dzn_dir:
        files = sorted(Path(dzn_dir).rglob("*.dzn"))
        if not files:
            raise FileNotFoundError(f"No .dzn files found in {dzn_dir}")
        return files
    raise ValueError("Provide dzn_files or dzn_dir.")



def benchmark_single_run(
    *,
    mzn_content: str,
    dzn_file: Path,
    solver: str,
    timeout_s: float,
    run_id: int,
    instance_name: str,
    objective_sense: ObjectiveSense,
) -> RunResult:
    def _sparsify_objective_trace(
        trace: list[tuple[float, float]],
        *,
        min_bucket_width: float = 1.0,
        alpha: float = 0.01,
    ) -> list[tuple[float, float]]:
        """
        Reduce an objective trace to a subsequence using geometric time bucketing.

        Keeps the first entry, then repeatedly jumps forward within buckets of size:
          max(min_bucket_width, cursor_time * alpha)
        and keeps the last point within each bucket (or cursor+1 if bucket is empty).

        While keeping entries, timestamps are rounded to 2 decimal places.
        """
        n = len(trace)
        if n == 0:
            return []

        kept: list[tuple[float, float]] = []
        cursor_idx = 0
        last_kept_idx = 0

        t0, v0 = trace[0]
        kept.append((round(float(t0), 2), v0))

        while cursor_idx < n - 1:
            cursor_time = float(trace[cursor_idx][0])
            bucket_end = cursor_time + max(float(min_bucket_width), cursor_time * float(alpha))

            scan_idx = cursor_idx + 1
            last_in_bucket_idx: Optional[int] = None
            while scan_idx < n and float(trace[scan_idx][0]) <= bucket_end:
                last_in_bucket_idx = scan_idx
                scan_idx += 1

            next_idx = last_in_bucket_idx if last_in_bucket_idx is not None else (cursor_idx + 1)
            cursor_idx = next_idx
            last_kept_idx = cursor_idx

            t, v = trace[cursor_idx]
            kept.append((round(float(t), 2), v))

        if last_kept_idx != n - 1:
            t_last, v_last = trace[-1]
            kept.append((round(float(t_last), 2), v_last))

        return kept

    with tempfile.TemporaryDirectory() as tmpdir_str:
        tmpdir = Path(tmpdir_str)

        minizinc_exe = os.environ.get("MINIZINC_EXECUTABLE", "minizinc")

        mzn_path = tmpdir / "model.mzn"
        mzn_path.write_text(mzn_content, encoding="utf-8")

        dzn_path = tmpdir / dzn_file.name
        shutil.copy(dzn_file, dzn_path)

        compile_time_s = 0.0


        solve_start = time.time()
        solve_exit: Optional[int] = None
        solve_timed_out = False
        stop_after_first_solution = False
        random_seed = int.from_bytes(hashlib.blake2b(f"{instance_name}\0{run_id}".encode(), digest_size=3).digest(), "big")

        first_solution_time_s: Optional[float] = None
        objective_trace: list[tuple[float, float]] = []
        best_obj: Optional[float] = None
        best_obj_time_s: Optional[float] = None
        saw_solution = False
        saw_optimal_marker = False
        saw_unknown_marker = False
        saw_error_marker = False
        current_solution_lines: list[str] = []

        stdout_tail_chunks: deque[str] = deque()
        stdout_tail_len = 0
        TAIL_MAX_CHARS = 1024 * 20

        def _append_stdout_tail(chunk: str) -> None:
            nonlocal stdout_tail_len
            if not chunk:
                return
            stdout_tail_chunks.append(chunk)
            stdout_tail_len += len(chunk)
            while stdout_tail_len > TAIL_MAX_CHARS and stdout_tail_chunks:
                removed = stdout_tail_chunks.popleft()
                stdout_tail_len -= len(removed)

        def _is_improvement(obj: float) -> bool:
            nonlocal best_obj
            if best_obj is None:
                return True
            if objective_sense == ObjectiveSense.MIN:
                return obj < best_obj
            return obj > best_obj

        def _parse_solution_blob(now_s: float) -> Optional[dict[str, Any]]:
            nonlocal first_solution_time_s, saw_solution
            blob = "\n".join(current_solution_lines).strip()
            current_solution_lines.clear()
            if not blob:
                return None
            try:
                data = json.loads(blob)
            except json.JSONDecodeError:
                return None
            if not isinstance(data, dict):
                return None
            saw_solution = True
            if first_solution_time_s is None:
                first_solution_time_s = float(now_s)
            return data

        try:
            solve_cmd = [
                minizinc_exe,
                "-a",
                "--solver",
                solver,
                "-f",
                "--statistics",
                "--compiler-statistics",
                "--no-output-ozn",
                "--output-mode", "json",
                "--output-objective",
                str(mzn_path),
                str(dzn_path),
                "--time-limit",
                str(int(timeout_s * 1000)),
                "--random-seed",
                str(int(random_seed)),
            ]

            proc = subprocess.Popen(
                solve_cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                cwd=str(tmpdir),
                text=True,
                bufsize=1,
                encoding="utf-8",
                errors="replace",
            )
            sent_sigint = False
            should_stop = False

            def try_parse_solution():
                nonlocal stop_after_first_solution, should_stop, best_obj, best_obj_time_s, objective_trace
                now_s = time.time() - solve_start
                data = _parse_solution_blob(now_s)
                if data is not None:
                    if "_objective" not in data:
                        # Satisfaction problem: stop immediately after first solution.
                        stop_after_first_solution = True
                        should_stop = True
                    else:
                        if stop_after_first_solution:
                            should_stop = True
                        obj = float(data["_objective"])
                        if _is_improvement(obj):
                            objective_trace.append((float(now_s), float(obj)))
                            best_obj = float(obj)
                            best_obj_time_s = float(now_s)


            def handle_stdout_line(line: str) -> None:
                nonlocal saw_optimal_marker, saw_unknown_marker, saw_error_marker
                nonlocal stop_after_first_solution, should_stop, best_obj, best_obj_time_s
                nonlocal compile_time_s

                if line.startswith("%"):
                    # MiniZinc statistics (from --statistics / --compiler-statistics).
                    # Example lines:
                    #   %%%mzn-stat: flatTime=0.169678
                    #   %%%mzn-stat-end
                    if line.startswith("%%%mzn-stat:"):
                        _prefix, _sep, rest = line.partition(":")
                        rest = rest.strip()
                        key, _eq, value_str = rest.partition("=")
                        key = key.strip()
                        value_str = value_str.strip()
                        if key == "flatTime" and value_str:
                            try:
                                value = float(value_str)
                            except (TypeError, ValueError):
                                value = None
                            if value is not None and value >= 0.0:
                                compile_time_s = value
                    return

                stripped = line.strip()


                # Solution delimiters / status markers
                if stripped in {"----------", "=========="}:
                    try_parse_solution()

                    if stripped == "==========":
                        saw_optimal_marker = True
                    return

                if stripped == "=====UNKNOWN=====":
                    saw_unknown_marker = True
                    return
                if stripped == "=====UNSATISFIABLE=====":
                    # Closed instance (optimal/complete) without a solution.
                    saw_optimal_marker = True
                    return
                if stripped in {
                    "=====ERROR=====",
                    "=====UNSATorUNBOUNDED=====",
                    "=====UNBOUNDED=====",
                }:
                    saw_error_marker = True
                    return

                # Regular output line (part of JSON solution or other text)
                current_solution_lines.append(line)

            for raw_line in proc.stdout:
                _append_stdout_tail(raw_line)
                handle_stdout_line(raw_line.rstrip("\n").rstrip("\r"))

                if should_stop and not sent_sigint and proc.poll() is None:
                    sent_sigint = True
                    try:
                        proc.send_signal(signal.SIGINT)
                    except Exception:  # noqa: BLE001
                        proc.kill()

            # If we ended without seeing a delimiter, try to parse whatever we buffered.
            if current_solution_lines:
                try_parse_solution()

            try:
                proc.wait(timeout=5.0)
            except subprocess.TimeoutExpired:
                proc.kill()
                time.sleep(5.0)


            stderr_txt = proc.stderr.read() if proc.returncode is not None else ""
            solve_exit = int(proc.returncode) if proc.returncode is not None else None
            solve_time_s = time.time() - solve_start
        except subprocess.TimeoutExpired:
            solve_time_s = time.time() - solve_start
            solve_timed_out = True

        # Determine status from streamed markers.
        if saw_error_marker:
            status = SolveStatus.ERROR
        elif stop_after_first_solution and saw_solution:
            # Satisfaction problem: we intentionally stop at the first solution, so
            # treat this as FEASIBLE regardless of whether the solver later prints
            # completion markers.
            status = SolveStatus.FEASIBLE
        elif saw_optimal_marker:
            status = SolveStatus.OPTIMAL
        elif saw_solution:
            status = SolveStatus.FEASIBLE
        elif proc.returncode is None or proc.returncode != 0:
            status = SolveStatus.ERROR
        else:
            status = SolveStatus.TIMEOUT

        objective_trace = _sparsify_objective_trace(
            objective_trace,
            min_bucket_width=1.0,
            alpha=0.01,
        )

        objective_value: Optional[float]
        objective_value_time_s: Optional[float]
        if objective_trace:
            objective_value = float(objective_trace[-1][1])
            objective_value_time_s = float(objective_trace[-1][0])
        else:
            objective_value = None
            objective_value_time_s = None

        # For satisfaction problems (no objective), we stop at the first solution and
        # use that time as the solve time.
        if len(objective_trace) == 0 and first_solution_time_s is not None:
            solve_time_s = float(first_solution_time_s)

        error = status == SolveStatus.ERROR
        error_message: Optional[str] = None
        if error:
            stdout_txt = "".join(stdout_tail_chunks)
            error_message = (
                "(((( cmd ))))\n\n"
                + " ".join(solve_cmd)
                + "\n\n"
                + "(((( STDOUT (tail) ))))\n\n"
                + stdout_txt.strip()
                + "\n\n"
                + "(((( STDERR ))))\n\n"
                + stderr_txt.strip()
            )[: 1024 * 32]


        return RunResult(
            instance=instance_name,
            run_id=run_id,
            status=status,
            objective_value=objective_value,
            objective_trace=objective_trace,
            first_solution_time_s=first_solution_time_s,
            objective_value_time_s=objective_value_time_s,
            compile_time_s=compile_time_s,
            solve_time_s=solve_time_s,
            error=error,
            error_message=error_message,
            minizinc_exit_code=(None if solve_timed_out else solve_exit),
        )


def _benchmark_single_run_slurm_worker(
    mzn_file: str,
    dzn_file: str,
    solver: str,
    timeout_s: float,
    run_id: int,
    instance_name: str,
    objective_sense: str,
) -> RunResult:
    """Submitit/Slurm worker wrapper (must be top-level for pickling)."""
    mzn_content = Path(mzn_file).read_text(encoding="utf-8")
    return benchmark_single_run(
        mzn_content=mzn_content,
        dzn_file=Path(dzn_file),
        solver=solver,
        timeout_s=float(timeout_s),
        run_id=int(run_id),
        instance_name=str(instance_name),
        objective_sense=ObjectiveSense(str(objective_sense)),
    )


def benchmark_model(
    *,
    mzn_content: str,
    solver: str,
    timeout_s: float,
    runs_per_instance: int,
    dzn_files: Optional[list[Path]] = None,
    dzn_dir: Optional[Path] = None,
    parallelism: Optional[int] = None,
    objective_sense: ObjectiveSense = ObjectiveSense.MIN,
    use_slurm: bool = False,
) -> BenchmarkResult:
    files = _discover_dzn_files(dzn_files, dzn_dir)
    effective_parallelism: Optional[int] = None
    if not use_slurm:
        effective_parallelism = int(parallelism or psutil.cpu_count(logical=False) or 1)
        effective_parallelism = max(effective_parallelism, 1)
    runs_per_instance = max(int(runs_per_instance), 1)

    # Use relative paths as instance names when dzn_dir is provided to handle
    # subdirectories with duplicate filenames; otherwise use just the filename.
    if dzn_dir is not None:
        base = Path(dzn_dir).resolve()
        instance_names = [f.resolve().relative_to(base).as_posix() for f in files]
    else:
        instance_names = [f.name for f in files]

    tasks: list[tuple[Path, int, str]] = []
    for f, inst_name in zip(files, instance_names, strict=True):
        for run_id in range(runs_per_instance):
            tasks.append((f, run_id, inst_name))

    log.info(
        "Starting MiniZinc benchmark",
        solver=solver,
        timeout_s=timeout_s,
        runs_per_instance=runs_per_instance,
        instances=len(files),
        tasks=len(tasks),
        parallelism=effective_parallelism,
        use_slurm=bool(use_slurm),
    )

    runs_by_instance: dict[str, list[RunResult]] = {name: [] for name in instance_names}

    if not use_slurm:

        with ThreadPoolExecutor(max_workers=effective_parallelism) as ex:
            futs = [
                ex.submit(
                    benchmark_single_run,
                    mzn_content=mzn_content,
                    dzn_file=dzn_file,
                    solver=solver,
                    timeout_s=timeout_s,
                    run_id=run_id,
                    instance_name=instance_name,
                    objective_sense=objective_sense,
                )
                for (dzn_file, run_id, instance_name) in tasks
            ]
            for fut in as_completed(futs):
                rr = fut.result()
                runs_by_instance[rr.instance].append(rr)
    else:

        submitit_folder = create_slurm_tmp_folder()
        try:
            mzn_file = submitit_folder / "model.mzn"
            mzn_file.write_text(mzn_content, encoding="utf-8")

            executor = submitit.AutoExecutor(folder=str(submitit_folder), cluster="slurm")
            configure_executor(executor, timeout_s=timeout_s)
            executor.update_parameters(slurm_array_parallelism=len(tasks))

            mzn_file_str = str(mzn_file)
            dzn_file_strs = [str(p.resolve()) for (p, _run_id, _inst) in tasks]
            run_ids = [int(run_id) for (_p, run_id, _inst) in tasks]
            insts = [str(inst) for (_p, _run_id, inst) in tasks]
            jobs = executor.map_array(
                _benchmark_single_run_slurm_worker,
                [mzn_file_str] * len(tasks),
                dzn_file_strs,
                [str(solver)] * len(tasks),
                [float(timeout_s)] * len(tasks),
                run_ids,
                insts,
                [objective_sense.value] * len(tasks),
            )

            for (dzn_file, run_id, instance_name), job in zip(tasks, jobs, strict=True):
                try:
                    rr = job.result()
                except Exception as exc:  # noqa: BLE001
                    job_id = getattr(job, "job_id", None)
                    msg = f"Slurm job failed (job_id={job_id}, folder={submitit_folder}): {exc}"
                    rr = RunResult(
                        instance=str(instance_name),
                        run_id=int(run_id),
                        status=SolveStatus.ERROR,
                        objective_value=None,
                        compile_time_s=0.0,
                        solve_time_s=0.0,
                        error=True,
                        error_message=msg,
                        minizinc_exit_code=None,
                    )
                runs_by_instance[rr.instance].append(rr)
        finally:
            shutil.rmtree(submitit_folder, ignore_errors=True)

    for inst in instance_names:
        runs_by_instance[inst].sort(key=lambda r: r.run_id)

    return BenchmarkResult(
        solver=solver,
        timeout_s=float(timeout_s),
        runs_per_instance=runs_per_instance,
        objective_sense=objective_sense,
        instances=instance_names,
        runs_by_instance=runs_by_instance,
    )


def benchmark_mzn_file(
    *,
    mzn_file: Path,
    solver: str,
    timeout_s: float,
    runs_per_instance: int,
    dzn_files: Optional[list[Path]] = None,
    dzn_dir: Optional[Path] = None,
    parallelism: Optional[int] = None,
    objective_sense: ObjectiveSense = ObjectiveSense.MIN,
    use_slurm: bool = False,
) -> BenchmarkResult:
    """Benchmark a MiniZinc model file against a set of .dzn instances."""
    return benchmark_model(
        mzn_content=Path(mzn_file).read_text(encoding="utf-8"),
        solver=solver,
        timeout_s=timeout_s,
        runs_per_instance=runs_per_instance,
        dzn_files=dzn_files,
        dzn_dir=dzn_dir,
        parallelism=parallelism,
        objective_sense=objective_sense,
        use_slurm=use_slurm,
    )


def compare_run_results(
    incumbent: RunResult,
    new: RunResult,
    *,
    objective_sense: ObjectiveSense,
    score_mode: ScoreMode = ScoreMode.MINIZINC_SOFT,
    temp_opt_time: float = 1.0,
    temp_objective: float = 10.0,
    timeout_s: float | None = None,
) -> RunComparison:
    """Compare two runs using MiniZinc Challenge-style pairwise Borda scoring.

    Returns a pair of scores (incumbent_score, new_score), plus a reason.

    For score modes MINIZINC and MINIZINC_SOFT, scores are in [0,1] and intended
    to be summed across run pairs (pairwise Borda-style).

    For score mode MINIZINC_AREA, scores are *area f-values* (lower is better) and
    intended to be summed directly (MiniZinc Challenge "area" procedure).

    Rules (pairwise version):
    - If one run is a better answer, it gets 1 and the other 0.
    - If answers are indistinguishable and both are solved, score is based on time:
        s scores t_other / (t_self + t_other) (0.5 if both are 0).
    - If a run is not solved, it always scores 0 (even if the other also fails).

    Project-specific scoring options:
    - score_mode=MINIZINC: exact MiniZinc Challenge scoring (time fractions with fixed
      temperature=1). Ignores temp_* parameters.
    - score_mode=MINIZINC_SOFT: current behavior; uses interpolation for objective/time
      comparisons controlled by temp_* parameters.
    - score_mode=MINIZINC_AREA: area scoring based on objective traces. Ignores temp_*
      parameters.
    """

    def _soft_ratio_scores(a_inc: float, a_new: float, *, temperature: float) -> tuple[float, float]:
        """Return a^t/(a^t+b^t) scores stably for nonnegative magnitudes."""
        a_inc = max(float(a_inc), 0.0)
        a_new = max(float(a_new), 0.0)
        if a_inc <= 0.0 and a_new <= 0.0:
            return 0.5, 0.5
        if a_inc <= 0.0:
            return 0.0, 1.0
        if a_new <= 0.0:
            return 1.0, 0.0
        log_inc = temperature * math.log(a_inc)
        log_new = temperature * math.log(a_new)
        m = max(log_inc, log_new)
        w_inc = math.exp(log_inc - m)
        w_new = math.exp(log_new - m)
        denom = w_inc + w_new
        return (w_inc / denom, w_new / denom)

    def solved(rr: RunResult) -> bool:
        # "Solved" means the run produced at least one solution (FEASIBLE) or proved
        # optimality (OPTIMAL). TIMEOUT/ERROR are treated as unsolved.
        return rr.status in (SolveStatus.FEASIBLE, SolveStatus.OPTIMAL)

    if score_mode == ScoreMode.MINIZINC_AREA and timeout_s is None:
        raise ValueError("timeout_s is required for MINIZINC_AREA scoring.")

    def time_scores(t_inc: float, t_new: float) -> tuple[float, float]:
        if score_mode == ScoreMode.MINIZINC_SOFT:
            return _soft_ratio_scores(t_new, t_inc, temperature=temp_opt_time)
        # MiniZinc Challenge time tie-break is the same ratio with temperature=1.
        return _soft_ratio_scores(t_new, t_inc, temperature=1.0)

    def solution_time(rr: RunResult) -> float:
        if rr.first_solution_time_s is not None:
            return float(rr.first_solution_time_s)
        return float(rr.solve_time_s)

    def objective_time(rr: RunResult) -> float:
        if rr.objective_value_time_s is not None:
            return float(rr.objective_value_time_s)
        if rr.objective_trace:
            return float(rr.objective_trace[-1][0])
        return float(rr.solve_time_s)

    def time_used(rr: RunResult) -> float:
        return float(rr.solve_time_s)

    def _objective_is_better(inc_obj: float, new_obj: float) -> bool:
        if objective_sense == ObjectiveSense.MIN:
            return inc_obj < new_obj
        return inc_obj > new_obj

    def _objective_to_min_quality(obj: float) -> float:
        # Convert objectives to a minimization "quality" (lower is better),
        # for use by MINIZINC_AREA scoring.
        return float(obj) if objective_sense == ObjectiveSense.MIN else -float(obj)

    def _effective_time_used_area(rr: RunResult) -> float:
        # For MINIZINC_AREA, unsolved and ERROR runs are treated as running the full timeout.
        if solved(rr):
            return max(float(rr.solve_time_s), 0.0)
        return max(float(timeout_s), 0.0)  # type: ignore[arg-type]

    def _objective_events_area(rr: RunResult) -> tuple[np.ndarray, np.ndarray]:
        """
        Return (t_s, q_s) for objective solutions, where q is a minimization "quality".
        Only returns events for solved (FEASIBLE/OPTIMAL) runs. For unsolved/ERROR runs,
        returns empty arrays (they are handled as 'stuck at UB').
        """
        if not solved(rr):
            return (np.asarray([], dtype=float), np.asarray([], dtype=float))

        t_used = _effective_time_used_area(rr)

        if rr.objective_trace:
            arr = np.asarray(rr.objective_trace, dtype=float)
            if arr.ndim != 2 or arr.shape[1] != 2:
                return (np.asarray([], dtype=float), np.asarray([], dtype=float))
            t_s = arr[:, 0]
            obj = arr[:, 1]
        elif rr.objective_value is not None:
            t0 = rr.objective_value_time_s
            if t0 is None:
                t0 = rr.first_solution_time_s
            if t0 is None:
                t0 = rr.solve_time_s
            if t0 is None:
                return (np.asarray([], dtype=float), np.asarray([], dtype=float))
            t_s = np.asarray([float(t0)], dtype=float)
            obj = np.asarray([float(rr.objective_value)], dtype=float)
        else:
            return (np.asarray([], dtype=float), np.asarray([], dtype=float))

        mask = np.isfinite(t_s) & np.isfinite(obj)
        if not bool(mask.any()):
            return (np.asarray([], dtype=float), np.asarray([], dtype=float))

        t_s = np.maximum(t_s[mask], 0.0)
        obj = obj[mask]

        mask = t_s <= t_used
        if not bool(mask.any()):
            return (np.asarray([], dtype=float), np.asarray([], dtype=float))
        t_s = t_s[mask]
        obj = obj[mask]

        order = np.argsort(t_s, kind="stable")
        t_s = t_s[order]
        obj = obj[order]

        q_s = obj if objective_sense == ObjectiveSense.MIN else -obj
        return (t_s.astype(float, copy=False), q_s.astype(float, copy=False))

    def _area_score_minimization(rr: RunResult, *, ub: float, lb: float) -> float:
        """
        MiniZinc Challenge-style area score for one run (minimization form), computed
        as the integral of a piecewise-constant penalty over [0, timeUsed].

        Penalty is UB until the first solution, then the quality of the last solution
        found (in minimization form). If no solution is found, penalty stays at UB.
        """
        t_used = _effective_time_used_area(rr)
        denom = float(ub - lb + 1.0)
        if not np.isfinite(denom) or denom <= 0.0:
            denom = 1.0

        t_s, q_s = _objective_events_area(rr)
        if t_s.size == 0:
            t_first = float(t_used)
            area = float(ub) * float(t_used)
        else:
            t_first = float(t_s[0])
            times = np.concatenate((np.asarray([0.0], dtype=float), t_s, np.asarray([t_used], dtype=float)))
            penalties = np.concatenate((np.asarray([float(ub)], dtype=float), q_s))
            dt = np.diff(times)
            if dt.size:
                dt = np.maximum(dt, 0.0)
            area = float(np.dot(penalties, dt))

        return 0.25 * t_first + 0.5 * (area / denom) + 0.25 * float(t_used)

    def _area_score_pair(inc_rr: RunResult, new_rr: RunResult) -> tuple[float, float] | None:
        """
        Compute (f_inc, f_new) for MINIZINC_AREA on optimization problems.

        Returns None if neither run contains objective information (satisfaction/UNSAT),
        in which case scoring falls back to timeUsed-only.
        """
        inc_t, inc_q = _objective_events_area(inc_rr)
        new_t, new_q = _objective_events_area(new_rr)

        bounds_first: list[float] = []
        bounds_best: list[float] = []
        if inc_q.size:
            bounds_first.append(float(inc_q[0]))
            bounds_best.append(float(np.min(inc_q)))
        if new_q.size:
            bounds_first.append(float(new_q[0]))
            bounds_best.append(float(np.min(new_q)))

        if not bounds_first or not bounds_best:
            return None

        ub = max(bounds_first)
        lb = min(bounds_best)
        return (
            _area_score_minimization(inc_rr, ub=ub, lb=lb),
            _area_score_minimization(new_rr, ub=ub, lb=lb),
        )

    inc_solved = solved(incumbent)
    new_solved = solved(new)

    # MINIZINC_AREA: return per-run f scores (lower is better), to be summed.
    if score_mode == ScoreMode.MINIZINC_AREA:
        if not inc_solved and not new_solved:
            # Both solvers timed out or errored -> ignore this pair with (0,0).
            # (Request: it's OK that this makes the instance effectively ignored.)
            return RunComparison(incumbent_score=0.0, new_score=0.0, reason="area both unsolved")

        pair = _area_score_pair(incumbent, new)
        if pair is None:
            # Satisfaction/UNSAT style (no objective trace): f(p,s) = timeUsed(p,s).
            # (For unsolved/ERROR, timeUsed is treated as the full timeout.)
            inc_f = _effective_time_used_area(incumbent)
            new_f = _effective_time_used_area(new)
        else:
            # Optimization: compute MiniZinc "area" f using objective traces and shared (UB, LB).
            inc_f, new_f = pair

        return RunComparison(incumbent_score=float(inc_f), new_score=float(new_f), reason="area f")

    if not inc_solved and not new_solved:
        # Both runs timed out or errored -> no one gets points in pairwise Borda.
        return RunComparison(incumbent_score=0.0, new_score=0.0, reason="both unsolved")
    if inc_solved and not new_solved:
        # Only incumbent produced a solution / proved optimality.
        return RunComparison(incumbent_score=1.0, new_score=0.0, reason="solved>unsolved")
    if new_solved and not inc_solved:
        # Only new produced a solution / proved optimality.
        return RunComparison(incumbent_score=0.0, new_score=1.0, reason="unsolved<solved")

    # Both solved.
    if score_mode == ScoreMode.MINIZINC_SOFT:
        if temp_opt_time <= 0.0 or not np.isfinite(temp_opt_time):
            raise ValueError(f"temp_opt_time must be > 0 and finite, got {temp_opt_time!r}")
        if temp_objective <= 0.0 or not np.isfinite(temp_objective):
            raise ValueError(f"temp_objective must be > 0 and finite, got {temp_objective!r}")

    inc_opt = incumbent.status == SolveStatus.OPTIMAL
    new_opt = new.status == SolveStatus.OPTIMAL

    # MINIZINC / MINIZINC_SOFT: keep the existing hierarchy (optimal > nonoptimal).
    if inc_opt and not new_opt:
        return RunComparison(incumbent_score=1.0, new_score=0.0, reason="optimal>nonoptimal")
    if new_opt and not inc_opt:
        return RunComparison(incumbent_score=0.0, new_score=1.0, reason="nonoptimal<optimal")

    inc_obj = incumbent.objective_value
    new_obj = new.objective_value

    # Both OPTIMAL: compare by runtime.
    if inc_opt and new_opt:
        inc_score, new_score = time_scores(time_used(incumbent), time_used(new))
        return RunComparison(incumbent_score=inc_score, new_score=new_score, reason="optimal time")

    # Both FEASIBLE: compare by objective when available, otherwise by time-to-solution.
    if inc_obj is not None and new_obj is not None:
        if inc_obj != new_obj:
            if score_mode == ScoreMode.MINIZINC:
                inc_better = _objective_is_better(float(inc_obj), float(new_obj))
                return RunComparison(
                    incumbent_score=(1.0 if inc_better else 0.0),
                    new_score=(0.0 if inc_better else 1.0),
                    reason="objective minizinc",
                )

            # MINIZINC_SOFT: interpolate objective differences.
            if objective_sense == ObjectiveSense.MIN:
                # Smaller objective is better; score by opposing penalty.
                inc_score, new_score = _soft_ratio_scores(
                    new_obj,
                    inc_obj,
                    temperature=temp_objective,
                )
            else:
                inc_score, new_score = _soft_ratio_scores(
                    inc_obj,
                    new_obj,
                    temperature=temp_objective,
                )
            return RunComparison(incumbent_score=inc_score, new_score=new_score, reason="objective soft")

        # Equal objective: tie-break by when that objective was reached.
        if score_mode == ScoreMode.MINIZINC:
            inc_score, new_score = _soft_ratio_scores(time_used(new), time_used(incumbent), temperature=1.0)
            return RunComparison(incumbent_score=inc_score, new_score=new_score, reason="feasible objective tie timeUsed")
        inc_score, new_score = time_scores(objective_time(incumbent), objective_time(new))
        return RunComparison(incumbent_score=inc_score, new_score=new_score, reason="feasible objective tie time")

    # Satisfaction (no objective): tie-break by time to first solution.
    if score_mode == ScoreMode.MINIZINC:
        inc_score, new_score = _soft_ratio_scores(time_used(new), time_used(incumbent), temperature=1.0)
        return RunComparison(incumbent_score=inc_score, new_score=new_score, reason="feasible timeUsed")
    inc_score, new_score = time_scores(solution_time(incumbent), solution_time(new))
    return RunComparison(incumbent_score=inc_score, new_score=new_score, reason="feasible time")


def compare_benchmark_results(
    *,
    incumbent: BenchmarkResult,
    new: BenchmarkResult,
    score_mode: ScoreMode = ScoreMode.MINIZINC_SOFT,
    score_temperature_opt_time: float = 1.0,
    score_temperature_objective: float = 10.0,
) -> BenchmarkComparison:
    if incumbent.instances != new.instances:
        raise ValueError("Cannot compare BenchmarkResult objects with different instances.")
    if incumbent.runs_per_instance != new.runs_per_instance:
        raise ValueError("Cannot compare BenchmarkResult objects with different runs_per_instance.")

    per_instance: dict[str, dict[str, float]] = {}
    incumbent_score = 0.0
    new_score = 0.0
    total = 0

    for inst in incumbent.instances:
        inc_runs = incumbent.runs_by_instance.get(inst, [])
        new_runs = new.runs_by_instance.get(inst, [])
        if len(inc_runs) != len(new_runs):
            raise ValueError(f"Cannot compare instance {inst}: different run counts.")

        inst_inc_score = 0.0
        inst_new_score = 0.0
        inst_total = 0
        for r_inc, r_new in zip(inc_runs, new_runs, strict=True):
            cmp = compare_run_results(
                r_inc,
                r_new,
                objective_sense=incumbent.objective_sense,
                score_mode=score_mode,
                temp_opt_time=score_temperature_opt_time,
                temp_objective=score_temperature_objective,
                timeout_s=max(float(incumbent.timeout_s), float(new.timeout_s)),
            )

            # MINIZINC_AREA: some pairs are intentionally treated as "ignored" by returning (0,0)
            # (e.g., both solvers timed out/errored).
            if (
                score_mode == ScoreMode.MINIZINC_AREA
                and float(cmp.incumbent_score) == 0.0
                and float(cmp.new_score) == 0.0
            ):
                continue

            inst_total += 1
            total += 1
            incumbent_score += float(cmp.incumbent_score)
            new_score += float(cmp.new_score)
            inst_inc_score += float(cmp.incumbent_score)
            inst_new_score += float(cmp.new_score)

        per_instance[inst] = {
            "incumbent_score": inst_inc_score,
            "new_score": inst_new_score,
            "total_compared": float(inst_total),
        }

    incumbent_avg_score = incumbent_score / total if total else 0.0
    new_avg_score = new_score / total if total else 0.0
    return BenchmarkComparison(
        score_mode=score_mode.value,
        incumbent_score=incumbent_score,
        new_score=new_score,
        total_compared=total,
        incumbent_avg_score=incumbent_avg_score,
        new_avg_score=new_avg_score,
        per_instance=per_instance,
    )


def wilcoxon_test_benchmark_comparison(cmp: BenchmarkComparison) -> WilcoxonResult:
    """One-sided Wilcoxon signed-rank test on per-instance averaged scores.

    We treat each MiniZinc instance as one independent sample by averaging the per-run scores
    (runs_per_instance) within that instance before applying Wilcoxon.
    """
    inc_vals: list[float] = []
    new_vals: list[float] = []

    for inst in sorted(cmp.per_instance.keys()):
        row = cmp.per_instance.get(inst) or {}
        total = float(row.get("total_compared") or 0.0)
        if total <= 0.0:
            continue
        inc_vals.append(float(row.get("incumbent_score") or 0.0) / total)
        new_vals.append(float(row.get("new_score") or 0.0) / total)

    n = len(inc_vals)
    if n == 0:
        return WilcoxonResult(p_value=1.0, n_instances=0, n_nonzero=0)

    # For MINIZINC and MINIZINC_SOFT, higher is better. For MINIZINC_AREA, lower is better.
    score_mode = ScoreMode(str(getattr(cmp, "score_mode", ScoreMode.MINIZINC_SOFT.value)))
    higher_is_better = score_mode != ScoreMode.MINIZINC_AREA
    diffs = [n_ - i_ for n_, i_ in zip(new_vals, inc_vals, strict=True)]
    n_nonzero = sum(1 for d in diffs if d != 0.0)
    if n_nonzero == 0:
        return WilcoxonResult(p_value=1.0, n_instances=n, n_nonzero=0)

    res = wilcoxon(
        new_vals,
        inc_vals,
        alternative=("greater" if higher_is_better else "less"),
        zero_method="wilcox",
        correction=False,
        method="auto",
    )
    return WilcoxonResult(p_value=float(res.pvalue), n_instances=n, n_nonzero=int(n_nonzero))
