from __future__ import annotations

import argparse
import json
import logging
import os
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Optional
import re

import structlog

from . import improver_llm
from . import minizinc_benchmark
from . import mzn_compiler
from . import verifier_llm
from .helpers_logging import setup_logging

log = structlog.get_logger()

# ============================================================================
# Defaults
# ============================================================================
DEFAULT_TOTAL_STEPS = 10
DEFAULT_SAMPLE_MODEL = "gpt-5.1"
DEFAULT_SAMPLE_REASONING_EFFORT = "high"
DEFAULT_SAMPLE_BATCH_SIZE = 3
DEFAULT_CUMULATIVE = True

DEFAULT_MINIZINC_MODEL = Path("./improver/osp/mip_model_obj_t2_search4.mzn")
DEFAULT_MINIZINC_DATA_DIR = Path("./improver/osp/instances_train/")
DEFAULT_MINIZINC_SOLVER = "chuffed"

DEFAULT_BENCHMARK_TIMEOUT_S = 60.0
DEFAULT_BENCHMARK_RUNS_PER_INSTANCE = 3
DEFAULT_BENCHMARK_ACCEPT_P_THRESHOLD = 0.05
DEFAULT_BENCHMARK_SCORE_MODE = minizinc_benchmark.ScoreMode.MINIZINC_SOFT.value
DEFAULT_BENCHMARK_SCORE_TEMPERATURE_OPT_TIME = 1.0
DEFAULT_BENCHMARK_SCORE_TEMPERATURE_OBJECTIVE = 10.0

DEFAULT_OUTPUT_FILE_TEMPLATE = "./improver/run_{YYYY-MM-DD}_{HH-MM-SS}.json"
DEFAULT_LOG_FILE_SUFFIX = ".log.jsonl"


@dataclass(frozen=True)
class WaterfallStage:
    model: str
    reasoning_effort: str
    max_runs: int
    parallelism: int
    max_turns: int


DEFAULT_VERIFIER_WATERFALL: list[WaterfallStage] = [
    #WaterfallStage("openai/gpt-5-mini", "high", max_runs=5, parallelism=5, max_turns=1),
    WaterfallStage("openrouter/deepseek/deepseek-v3.2", "medium", max_runs=16, parallelism=8, max_turns=5),
]

def _parse_waterfall_arg(arg: str) -> list[WaterfallStage]:
    stages: list[WaterfallStage] = []
    for part in (arg or "").split():
        fields = part.split(":")
        if len(fields) != 5:
            raise ValueError(
                "Invalid --verifier-waterfall format. Expected: "
                "'model:effort:max_runs:parallelism:max_turns ...'"
            )
        model, effort, max_runs, parallelism, max_turns = fields
        stages.append(WaterfallStage(
            model=model,
            reasoning_effort=effort,
            max_runs=int(max_runs),
            parallelism=int(parallelism),
            max_turns=int(max_turns),
        ))
    if not stages:
        raise ValueError("Empty --verifier-waterfall provided.")
    return stages


def _waterfall_from_state(run_args: dict[str, Any]) -> list[WaterfallStage]:
    raw = run_args.get("verifier_waterfall")
    if not raw:
        return list(DEFAULT_VERIFIER_WATERFALL)
    stages: list[WaterfallStage] = []
    for s in raw:
        stages.append(
            WaterfallStage(
                model=str(s["model"]),
                reasoning_effort=str(s["reasoning_effort"]),
                max_runs=int(s["max_runs"]),
                parallelism=int(s["parallelism"]),
                max_turns=int(s.get("max_turns", 1)),
            )
        )
    return stages


def _render_path_template(template: str, dt: datetime) -> Path:
    rendered = (
        template.replace("{YYYY-MM-DD}", dt.strftime("%Y-%m-%d"))
        .replace("{HH-MM-SS}", dt.strftime("%H-%M-%S"))
    )
    return Path(rendered)

def _derive_log_file_from_output(output_file: Path) -> Path:
    if output_file.suffix == ".json":
        return output_file.with_suffix(DEFAULT_LOG_FILE_SUFFIX)
    return output_file.with_name(output_file.name + DEFAULT_LOG_FILE_SUFFIX)


def _atomic_save_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    swap = path.with_suffix(path.suffix + ".swap")
    bak = path.with_suffix(path.suffix + ".bak")

    swap.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
    if bak.exists():
        bak.unlink()
    if path.exists():
        path.rename(bak)
    swap.rename(path)


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _normalize_code_for_dedupe(code: str) -> str:
    return " ".join((code or "").strip().split())


def _ensure_annotation_decl(mzn_content: str, annotation_name: str) -> str:
    decl = f"annotation {annotation_name};"
    if decl in mzn_content:
        return mzn_content
    return decl + "\n" + mzn_content.lstrip("\n")


def _append_constraint(
    *,
    mzn_content: str,
    constraint_code: str,
    name: str,
    description: str,
    keep_redundant_annotation: bool,
) -> str:
    base = mzn_content.rstrip("\n")
    code = " ".join((constraint_code or "").strip().split())

    if not code.endswith(";"):
        code += ";"

    if keep_redundant_annotation:
        base = _ensure_annotation_decl(base, "redundant")
        if "::redundant" not in code.replace(" ", ""):
            code = code[:-1].rstrip() + " ::redundant;"
    else:
        code = re.sub(r"\s*::\s*redundant\s*(?=;)", "", code).strip()

    comment = ""
    if name or description:
        tag = "autogenerated (candidate)" if keep_redundant_annotation else "autogenerated (accepted+proven)"
        comment = f"% {tag}: {name}: {description}".strip() + "\n"

    return f"{base}\n\n{comment}{code}\n"


def _summarize_benchmark(br: minizinc_benchmark.BenchmarkResult) -> str:
    counts: dict[str, int] = {s.value: 0 for s in minizinc_benchmark.SolveStatus}
    total = 0
    for inst in br.instances:
        for r in br.runs_by_instance.get(inst, []):
            counts[r.status.value] += 1
            total += 1
    return (
        f"solver={br.solver}, timeout_s={br.timeout_s}, runs_per_instance={br.runs_per_instance}\n"
        f"runs={total}, OPTIMAL={counts['OPTIMAL']}, FEASIBLE={counts['FEASIBLE']}, TIMEOUT={counts['TIMEOUT']}, ERROR={counts['ERROR']}"
    )


def _build_previous_attempts(state: dict[str, Any]) -> list[improver_llm.PreviousConstraintAttempt]:
    attempts: list[improver_llm.PreviousConstraintAttempt] = []
    for ev in state.get("evaluations", []):
        c = ev.get("constraint", {})
        attempts.append(
            improver_llm.PreviousConstraintAttempt(
                name=str(c.get("name", "")),
                description=str(c.get("description", "")),
                code=str(c.get("code", "")),
                outcome=str(ev.get("outcome", "")),
                incumbent_benchmark=minizinc_benchmark.BenchmarkResult.from_dict(ev.get("incumbent_benchmark", {})),
                new_benchmark=minizinc_benchmark.BenchmarkResult.from_dict(ev.get("new_benchmark", {})),
            )
        )
    return attempts


def _run_proof_waterfall(
    *,
    lean_code: str,
    stages: list[WaterfallStage],
) -> dict[str, Any]:
    from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

    all_attempts: dict[str, list[dict[str, Any]]] = {}
    total_attempts = 0

    for stage in stages:
        if stage.max_runs <= 0:
            continue
        max_runs = int(stage.max_runs)
        parallelism = max(1, min(int(stage.parallelism), max_runs))
        max_turns = int(stage.max_turns)

        log.info(
            "Waterfall stage start",
            model=stage.model,
            reasoning_effort=stage.reasoning_effort,
            max_runs=max_runs,
            parallelism=parallelism,
            max_turns=max_turns,
        )

        all_attempts.setdefault(stage.model, [])

        def task() -> dict[str, Any]:
            try:
                r = verifier_llm.prove_lean_code(
                    lean_code,
                    model_name=stage.model,
                    max_turns=max_turns,
                    reasoning_setting=stage.reasoning_effort,
                    capture_trace=True,
                )
                return {
                    "success": bool(r.success),
                    "total_cost_ct": float(r.total_cost_ct),
                    "turns_needed": int(r.turns_needed),
                    "llm_usage": r.llm_usage,
                    "trace": r.trace,
                }
            except Exception as exc:  # noqa: BLE001
                log.exception("Proof attempt crashed", model=stage.model, error=str(exc))
                return {"success": False, "error": str(exc)}

        success = False
        success_result: Optional[dict[str, Any]] = None

        with ThreadPoolExecutor(max_workers=parallelism) as ex:
            active = set()
            started = 0

            def schedule_one() -> None:
                nonlocal started
                active.add(ex.submit(task))
                started += 1

            for _ in range(min(parallelism, max_runs)):
                schedule_one()

            while active:
                done, _ = wait(active, return_when=FIRST_COMPLETED)
                for fut in done:
                    active.remove(fut)
                    total_attempts += 1
                    res = fut.result()
                    all_attempts[stage.model].append(res)
                    if res.get("success"):
                        success = True
                        success_result = res
                        for pending in active:
                            pending.cancel()
                        active.clear()
                        break
                    if started < max_runs:
                        schedule_one()
                if success:
                    break

        if success:
            return {
                "success": True,
                "model_used": stage.model,
                "attempts": total_attempts,
                "result": success_result,
                "all_attempts": all_attempts,
            }

        log.info("Waterfall stage exhausted", model=stage.model, attempts=len(all_attempts[stage.model]))

    return {"success": False, "model_used": "", "attempts": total_attempts, "result": None, "all_attempts": all_attempts}


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="AutoMZN constraint improver (benchmark-first, then prove)")
    p.add_argument("--total-steps", type=int, default=DEFAULT_TOTAL_STEPS)
    p.add_argument("--sample-model", type=str, default=DEFAULT_SAMPLE_MODEL)
    p.add_argument("--sample-reasoning-effort", type=str, default=DEFAULT_SAMPLE_REASONING_EFFORT)
    p.add_argument("--sample-batch-size", type=int, default=DEFAULT_SAMPLE_BATCH_SIZE)
    p.add_argument("--cumulative", action=argparse.BooleanOptionalAction, default=DEFAULT_CUMULATIVE)

    p.add_argument("--minizinc-model", type=Path, default=DEFAULT_MINIZINC_MODEL)
    p.add_argument("--minizinc-data-dir", type=Path, default=DEFAULT_MINIZINC_DATA_DIR)
    p.add_argument("--minizinc-solver", type=str, default=DEFAULT_MINIZINC_SOLVER)

    p.add_argument("--benchmark-timeout", type=float, default=DEFAULT_BENCHMARK_TIMEOUT_S)
    p.add_argument("--benchmark-runs-per-instance", type=int, default=DEFAULT_BENCHMARK_RUNS_PER_INSTANCE)
    p.add_argument("--benchmark-parallelism", type=int, default=None)
    p.add_argument(
        "--use-slurm",
        action="store_true",
        default=False,
        help="Run MiniZinc benchmarks via Slurm/submitit (one job per (instance, run_id)).",
    )
    p.add_argument(
        "--benchmark-score-mode",
        type=str,
        choices=sorted({m.value for m in minizinc_benchmark.ScoreMode} | {"soft", "hard"}),
        default=DEFAULT_BENCHMARK_SCORE_MODE,
        help=(
            "Scoring mode for benchmark comparisons. "
            "minizinc_soft uses temperature-smoothed comparisons (default; current behavior). "
            "minizinc matches the MiniZinc Challenge spec exactly (time fractions; ignores temperatures). "
            "minizinc_area uses area scoring based on objective traces (ignores temperatures). "
            "Back-compat aliases: soft->minizinc_soft, hard->minizinc."
        ),
    )
    p.add_argument(
        "--benchmark-accept-p-threshold",
        type=float,
        default=DEFAULT_BENCHMARK_ACCEPT_P_THRESHOLD,
        help="Accept a constraint if Wilcoxon p-value (one-sided, new>inc) is <= this threshold.",
    )
    p.add_argument(
        "--benchmark-score-temperature-opt-time",
        type=float,
        default=DEFAULT_BENCHMARK_SCORE_TEMPERATURE_OPT_TIME,
        help="Temperature exponent for soft optimal-time scoring: p^t/(p^t+q^t).",
    )
    p.add_argument(
        "--benchmark-score-temperature-objective",
        type=float,
        default=DEFAULT_BENCHMARK_SCORE_TEMPERATURE_OBJECTIVE,
        help="Temperature exponent for soft objective scoring: p^t/(p^t+q^t).",
    )

    p.add_argument(
        "--verifier-waterfall",
        type=str,
        default=None,
        help="Override default waterfall. Format: 'model:effort:max_runs:parallelism:max_turns ...'",
    )

    p.add_argument(
        "--log-file",
        type=str,
        default=None,
        help="Optional log file path. Defaults to --output-file with .json replaced by .jsonl.",
    )
    p.add_argument("--output-file", type=str, default=DEFAULT_OUTPUT_FILE_TEMPLATE)
    p.add_argument(
        "--output-model",
        type=str,
        default=None,
        help="Write final incumbent MiniZinc model to this file (only with --cumulative).",
    )

    p.add_argument("--verbose", action="store_true", default=False)
    args = p.parse_args()

    #if args.output_model and not args.cumulative:
   #     p.error("--output-model requires --cumulative")
    return args


def main() -> None:
    args = _parse_args()
    mzn_compiler.ensure_compiled()
    dt = datetime.now()
    out_file = _render_path_template(args.output_file, dt)
    output_model_file = _render_path_template(args.output_model, dt) if args.output_model else None

    log_file = (
        _render_path_template(args.log_file, dt)
        if args.log_file
        else _derive_log_file_from_output(out_file)
    )
    log_file_existed = log_file.exists()

    setup_logging(
        log_file=str(log_file),
        level=logging.DEBUG if args.verbose else logging.INFO,
        enable_thread_file_logging=False,
    )

    log.info(
        "Run marker",
        run_ts=dt.isoformat(),
        pid=os.getpid(),
        argv=list(sys.argv),
        output_file=str(out_file),
        output_model=(None if output_model_file is None else str(output_model_file)),
        log_file=str(log_file),
        log_file_existed=bool(log_file_existed),
    )
    if log_file_existed:
        log.info("Appending to existing log file", log_file=str(log_file))

    log.info(
        "Improver start",
        output_file=str(out_file),
        log_file=str(log_file),
        total_steps=args.total_steps,
        sample_model=args.sample_model,
        sample_batch_size=args.sample_batch_size,
        cumulative=bool(args.cumulative),
        output_model=(None if output_model_file is None else str(output_model_file)),
    )

    if out_file.exists():
        state = _load_json(out_file)
        log.info("Resuming from existing state", output_file=str(out_file))
        try:
            state_args = state.get("args") or {}
            requested_use_slurm = bool(args.use_slurm)
            existing_use_slurm = bool(state_args.get("use_slurm", False))
            if requested_use_slurm and not existing_use_slurm:
                state_args["use_slurm"] = True
                state["args"] = state_args
                state["updated_at"] = datetime.now().isoformat()
                _atomic_save_json(out_file, state)
                log.info(
                    "Enabled use_slurm on resume",
                    use_slurm=True,
                    output_file=str(out_file),
                )
            elif "use_slurm" not in state_args:
                state_args["use_slurm"] = requested_use_slurm
                state["args"] = state_args
                state["updated_at"] = datetime.now().isoformat()
                _atomic_save_json(out_file, state)
                log.info(
                    "Initialized missing use_slurm on resume",
                    use_slurm=bool(state_args["use_slurm"]),
                    output_file=str(out_file),
                )
            existing_total_steps = int(state_args.get("total_steps") or 0)
            requested_total_steps = int(args.total_steps)
            if requested_total_steps > existing_total_steps:
                state_args["total_steps"] = requested_total_steps
                state["args"] = state_args
                state["updated_at"] = datetime.now().isoformat()
                _atomic_save_json(out_file, state)
                log.info(
                    "Updated total_steps on resume",
                    previous_total_steps=existing_total_steps,
                    total_steps=requested_total_steps,
                    output_file=str(out_file),
                )
            else:
                log.info(
                    "Keeping existing total_steps on resume",
                    existing_total_steps=existing_total_steps,
                    requested_total_steps=requested_total_steps,
                    output_file=str(out_file),
                )
        except Exception as exc:  # noqa: BLE001
            log.exception(
                "Failed to update total_steps on resume",
                error=str(exc),
                requested_total_steps=int(args.total_steps),
                output_file=str(out_file),
            )
    else:
        original_content = args.minizinc_model.read_text(encoding="utf-8")
        waterfall = _parse_waterfall_arg(args.verifier_waterfall) if args.verifier_waterfall else list(DEFAULT_VERIFIER_WATERFALL)
        state = {
            "created_at": dt.isoformat(),
            "updated_at": dt.isoformat(),
            "args": {
                "total_steps": args.total_steps,
                "sample_model": args.sample_model,
                "sample_reasoning_effort": args.sample_reasoning_effort,
                "sample_batch_size": args.sample_batch_size,
                "cumulative": bool(args.cumulative),
                "minizinc_model": str(args.minizinc_model),
                "minizinc_data_dir": str(args.minizinc_data_dir),
                "minizinc_solver": args.minizinc_solver,
                "benchmark_timeout": args.benchmark_timeout,
                "benchmark_runs_per_instance": args.benchmark_runs_per_instance,
                "benchmark_parallelism": args.benchmark_parallelism,
                "use_slurm": bool(args.use_slurm),
                "benchmark_score_mode": str(args.benchmark_score_mode),
                "benchmark_accept_p_threshold": float(args.benchmark_accept_p_threshold),
                "benchmark_score_temperature_opt_time": float(args.benchmark_score_temperature_opt_time),
                "benchmark_score_temperature_objective": float(args.benchmark_score_temperature_objective),
                "verifier_waterfall": [asdict(s) for s in waterfall],
            },
            "original_mzn_content": original_content,
            "incumbent_mzn_content": original_content,
            "baseline_benchmark": None,
            "incumbent_benchmark": None,
            "sampling_calls": [],
            "pending_constraints": [],
            "evaluations": [],
        }
        _atomic_save_json(out_file, state)

    state.pop("in_progress", None)

    run_args = state.get("args") or {}
    waterfall = _waterfall_from_state(run_args)

    if output_model_file is not None and not bool(run_args.get("cumulative", False)):
        log.error(
            "--output-model requires cumulative mode for the active run",
            output_model=str(output_model_file),
            cumulative=bool(run_args.get("cumulative", False)),
        )
        raise SystemExit(2)

    def _maybe_write_output_model() -> None:
        if output_model_file is None:
            return
        final_model = str(state.get("incumbent_mzn_content", ""))
        output_model_file.parent.mkdir(parents=True, exist_ok=True)
        output_model_file.write_text(final_model, encoding="utf-8")
        log.info(
            "Wrote final incumbent MiniZinc model",
            output_model=str(output_model_file),
            chars=len(final_model),
        )

    # Preflight: ensure input MiniZinc compiles to Lean and the generated Lean is syntactically valid.
    try:
        with tempfile.TemporaryDirectory() as tmpdir_str:
            tmp_mzn = Path(tmpdir_str) / "preflight.mzn"
            tmp_mzn.write_text(state["original_mzn_content"], encoding="utf-8")
            preflight = mzn_compiler.mzn_to_lean(tmp_mzn, validate_lean=True)
        if not preflight.success:
            log.error(
                "Preflight failed: MiniZinc→Lean compilation or Lean validation failed",
                compiler_stdout=preflight.compiler_stdout,
                compiler_stderr=preflight.compiler_stderr,
            )
            _maybe_write_output_model()
            return
    except Exception as exc:  # noqa: BLE001
        log.exception("Preflight crashed", error=str(exc))
        _maybe_write_output_model()
        return

    # Benchmark baseline / incumbent if missing
    if state.get("baseline_benchmark") is None:
        baseline = minizinc_benchmark.benchmark_model(
            mzn_content=state["original_mzn_content"],
            solver=str(run_args["minizinc_solver"]),
            timeout_s=float(run_args["benchmark_timeout"]),
            runs_per_instance=int(run_args["benchmark_runs_per_instance"]),
            dzn_dir=Path(run_args["minizinc_data_dir"]),
            parallelism=run_args.get("benchmark_parallelism"),
            use_slurm=bool(run_args.get("use_slurm", False)),
        )
        state["baseline_benchmark"] = baseline.to_dict()
        state["incumbent_benchmark"] = baseline.to_dict()
        state["updated_at"] = datetime.now().isoformat()
        _atomic_save_json(out_file, state)
        log.info("Baseline benchmark complete", summary=_summarize_benchmark(baseline))

    evaluated = len(state.get("evaluations", []))
    dedupe: set[str] = {
        _normalize_code_for_dedupe(ev.get("constraint", {}).get("code", "")) for ev in state.get("evaluations", [])
    }
    dedupe |= {_normalize_code_for_dedupe(c.get("code", "")) for c in state.get("pending_constraints", [])}

    sampling_failures = 0

    while evaluated < int(run_args["total_steps"]):
        base_mzn = state["incumbent_mzn_content"] if run_args["cumulative"] else state["original_mzn_content"]
        incumbent_benchmark = minizinc_benchmark.BenchmarkResult.from_dict(state["incumbent_benchmark"])

        if not state["pending_constraints"]:
            previous = _build_previous_attempts(state)
            perf = _summarize_benchmark(incumbent_benchmark)

            with tempfile.TemporaryDirectory() as tmpdir_str:
                tmp_mzn = Path(tmpdir_str) / "model.mzn"
                tmp_mzn.write_text(base_mzn, encoding="utf-8")
                batch = improver_llm.elicit_redundant_constraints(
                    mzn_path=tmp_mzn,
                    model_name=run_args["sample_model"],
                    reasoning_effort=run_args["sample_reasoning_effort"],
                    num_constraints=run_args["sample_batch_size"],
                    previous_attempts=previous,
                )

            sample_call_id = len(state["sampling_calls"])
            state["sampling_calls"].append(
                {
                    "ts": datetime.now().isoformat(),
                    "model": run_args["sample_model"],
                    "reasoning_effort": run_args["sample_reasoning_effort"],
                    "batch_size": run_args["sample_batch_size"],
                    "llm_usage": batch.llm_usage,
                    "success": bool(batch.success),
                    "error_message": batch.error_message,
                }
            )

            if not batch.success:
                sampling_failures += 1
                state["updated_at"] = datetime.now().isoformat()
                _atomic_save_json(out_file, state)
                log.warning(
                    "Sampling failed",
                    error=batch.error_message,
                    sampling_failures=sampling_failures,
                )
                if sampling_failures >= 3:
                    log.error("Sampling failed too often; stopping", sampling_failures=sampling_failures)
                    _maybe_write_output_model()
                    return
                continue
            sampling_failures = 0

            for c in batch.constraints:
                code_key = _normalize_code_for_dedupe(c.constraint_code)
                if code_key in dedupe:
                    continue
                dedupe.add(code_key)
                state["pending_constraints"].append(
                    {
                        "name": c.constraint_name,
                        "description": c.constraint_description,
                        "code": c.constraint_code,
                        "sample_call_id": sample_call_id,
                    }
                )

            state["updated_at"] = datetime.now().isoformat()
            _atomic_save_json(out_file, state)
            log.info("Sampling added pending constraints", pending=len(state["pending_constraints"]))
            continue

        constraint = state["pending_constraints"].pop(0)
        eval_id = len(state.get("evaluations", []))
        start_ts = time.time()

        incumbent_mzn_content = base_mzn
        new_mzn_content = _append_constraint(
            mzn_content=incumbent_mzn_content,
            constraint_code=str(constraint["code"]),
            name=str(constraint.get("name", "")),
            description=str(constraint.get("description", "")),
            keep_redundant_annotation=True,
        )

        log.info("Evaluating constraint", eval_id=eval_id, constraint_name=constraint.get("name", ""))
        outcome = "UNKNOWN"
        bench_new: Optional[minizinc_benchmark.BenchmarkResult] = None
        bench_cmp: Optional[minizinc_benchmark.BenchmarkComparison] = None
        accepted_by_benchmark = False
        proof_info: dict[str, Any] | None = None
        wilcoxon_info: dict[str, Any] | None = None

        try:
            score_mode = minizinc_benchmark.ScoreMode(str(run_args.get("benchmark_score_mode", DEFAULT_BENCHMARK_SCORE_MODE)))
            bench_new = minizinc_benchmark.benchmark_model(
                mzn_content=new_mzn_content,
                solver=str(run_args["minizinc_solver"]),
                timeout_s=float(run_args["benchmark_timeout"]),
                runs_per_instance=int(run_args["benchmark_runs_per_instance"]),
                dzn_dir=Path(run_args["minizinc_data_dir"]),
                parallelism=run_args.get("benchmark_parallelism"),
                use_slurm=bool(run_args.get("use_slurm", False)),
            )
            bench_cmp = minizinc_benchmark.compare_benchmark_results(
                incumbent=incumbent_benchmark,
                new=bench_new,
                score_mode=score_mode,
                score_temperature_opt_time=float(
                    run_args.get(
                        "benchmark_score_temperature_opt_time",
                        DEFAULT_BENCHMARK_SCORE_TEMPERATURE_OPT_TIME,
                    )
                ),
                score_temperature_objective=float(
                    run_args.get(
                        "benchmark_score_temperature_objective",
                        DEFAULT_BENCHMARK_SCORE_TEMPERATURE_OBJECTIVE,
                    )
                ),
            )
            wilcoxon_res = minizinc_benchmark.wilcoxon_test_benchmark_comparison(bench_cmp)
            wilcoxon_info = wilcoxon_res.to_dict() | {
                "score_mode": score_mode.value,
                "score_temperature_opt_time": float(
                    run_args.get(
                        "benchmark_score_temperature_opt_time",
                        DEFAULT_BENCHMARK_SCORE_TEMPERATURE_OPT_TIME,
                    )
                ),
                "score_temperature_objective": float(
                    run_args.get(
                        "benchmark_score_temperature_objective",
                        DEFAULT_BENCHMARK_SCORE_TEMPERATURE_OBJECTIVE,
                    )
                ),
            }
        except Exception as exc:  # noqa: BLE001
            outcome = "BENCHMARK_ERROR"
            proof_info = {"error": str(exc)}
            log.exception("Benchmark failed", error=str(exc))
        else:
            p_threshold = float(run_args.get("benchmark_accept_p_threshold", DEFAULT_BENCHMARK_ACCEPT_P_THRESHOLD))
            p_value = float(wilcoxon_info.get("p_value")) if wilcoxon_info is not None else 1.0
            accepted_by_benchmark = p_value <= p_threshold

            if not accepted_by_benchmark:
                outcome = "BENCHMARK_FAIL"
            else:

                try:
                    with tempfile.TemporaryDirectory() as tmpdir_str:
                        tmp_mzn = Path(tmpdir_str) / "prove.mzn"
                        tmp_mzn.write_text(new_mzn_content, encoding="utf-8")
                        compile_res = mzn_compiler.mzn_to_lean(tmp_mzn, validate_lean=True)

                    if not compile_res.success:
                        outcome = "PROOF_ERROR"
                        proof_info = {
                            "compile_success": False,
                            "compiler_stdout": compile_res.compiler_stdout,
                            "compiler_stderr": compile_res.compiler_stderr,
                        }
                    else:
                        proof_wf = _run_proof_waterfall(
                            lean_code=compile_res.lean_code,
                            stages=waterfall,
                        )
                        proof_info = {"compile_success": True, "waterfall": proof_wf}
                        if proof_wf.get("success"):
                            outcome = "SUCCESS"
                            if run_args["cumulative"]:
                                incumbent_no_ann = _append_constraint(
                                    mzn_content=state["incumbent_mzn_content"],
                                    constraint_code=str(constraint["code"]),
                                    name=str(constraint.get("name", "")),
                                    description=str(constraint.get("description", "")),
                                    keep_redundant_annotation=False,
                                )
                                state["incumbent_mzn_content"] = incumbent_no_ann
                                state["incumbent_benchmark"] = (
                                    bench_new.to_dict() if bench_new is not None else state["incumbent_benchmark"]
                                )
                        else:
                            outcome = "PROOF_FAIL"
                except Exception as exc:  # noqa: BLE001
                    outcome = "PROOF_ERROR"
                    proof_info = {"error": str(exc)}
                    log.exception("Proof step crashed", error=str(exc))

        record = {
            "eval_id": eval_id,
            "ts_start": start_ts,
            "ts_end": time.time(),
            "constraint": constraint,
            "incumbent_mzn_content": incumbent_mzn_content,
            "new_mzn_content": new_mzn_content,
            "incumbent_benchmark": incumbent_benchmark.to_dict(),
            "new_benchmark": None if bench_new is None else bench_new.to_dict(),
            "benchmark_comparison": None if bench_cmp is None else bench_cmp.to_dict(),
            "benchmark_wilcoxon": wilcoxon_info,
            "accepted_by_benchmark": bool(accepted_by_benchmark),
            "outcome": outcome,
            "proof": proof_info,
        }
        state["evaluations"].append(record)
        state["updated_at"] = datetime.now().isoformat()
        _atomic_save_json(out_file, state)

        log.info(
            "Evaluation complete",
            eval_id=eval_id,
            outcome=outcome,
            elapsed_s=round(time.time() - start_ts, 3),
            benchmark_cmp=None if bench_cmp is None else bench_cmp.to_dict(),
        )

        evaluated = len(state.get("evaluations", []))

    _maybe_write_output_model()
    log.info("Done", evaluated=evaluated, output_file=str(out_file))


if __name__ == "__main__":
    main()
