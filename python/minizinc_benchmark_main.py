"""Resumable benchmark runner for one or two MiniZinc models."""

from __future__ import annotations

import argparse
import json
import logging
import math
import os
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

import structlog

from . import minizinc_benchmark
from .helpers_logging import setup_logging

log = structlog.get_logger()

DEFAULT_OUTPUT_FILE_TEMPLATE = "./improver/mzn_benchmark_{YYYY-MM-DD}_{HH-MM-SS}.json"
DEFAULT_LOG_FILE_SUFFIX = ".log.jsonl"

DEFAULT_MINIZINC_DATA_DIR = Path("./improver/osp/instances_train/")
DEFAULT_MINIZINC_SOLVER = "chuffed"
DEFAULT_BENCHMARK_TIMEOUT_S = 60.0
DEFAULT_BENCHMARK_RUNS_PER_INSTANCE = 3

STATUS_ORDER = [
    minizinc_benchmark.SolveStatus.OPTIMAL,
    minizinc_benchmark.SolveStatus.FEASIBLE,
    minizinc_benchmark.SolveStatus.TIMEOUT,
    minizinc_benchmark.SolveStatus.ERROR,
]
SAT_STATUSES = {minizinc_benchmark.SolveStatus.OPTIMAL, minizinc_benchmark.SolveStatus.FEASIBLE}


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


def _model_key(path: Path) -> str:
    # Preserve relative paths if the user provided them so JSON output is portable
    # across machines/workdirs. For absolute inputs, keep an absolute, normalized path.
    if path.is_absolute():
        return str(path.resolve())
    return os.path.normpath(str(path))


def _format_float(value: float | None, precision: int = 3) -> str:
    if value is None:
        return "-"
    return f"{value:.{precision}f}"


def _mean(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / len(values)


def _geomean(values: list[float]) -> float | None:
    if not values:
        return None
    if any(v < 0 for v in values):
        return None
    if any(v == 0 for v in values):
        return 0.0
    return math.exp(sum(math.log(v) for v in values) / len(values))


def _render_table(headers: list[str], rows: list[list[str]]) -> str:
    widths = [len(h) for h in headers]
    for row in rows:
        for idx, cell in enumerate(row):
            widths[idx] = max(widths[idx], len(cell))

    sep = "+-" + "-+-".join("-" * w for w in widths) + "-+"

    def fmt(row: list[str]) -> str:
        return "| " + " | ".join(cell.ljust(widths[i]) for i, cell in enumerate(row)) + " |"

    lines = [sep, fmt(headers), sep]
    lines.extend(fmt(row) for row in rows)
    lines.append(sep)
    return "\n".join(lines)


def _display_model_name(key: str, labels: dict[str, str]) -> str:
    label = labels.get(key, key)
    p = Path(label)
    return p.name or label


def _flatten_runs(
    result: minizinc_benchmark.BenchmarkResult,
) -> dict[tuple[str, int], minizinc_benchmark.RunResult]:
    out: dict[tuple[str, int], minizinc_benchmark.RunResult] = {}
    for instance in result.instances:
        for run in result.runs_by_instance.get(instance, []):
            out[(instance, run.run_id)] = run
    return out


def _status_counts(runs: list[minizinc_benchmark.RunResult]) -> dict[minizinc_benchmark.SolveStatus, int]:
    counts = {status: 0 for status in STATUS_ORDER}
    for run in runs:
        if run.status in counts:
            counts[run.status] += 1
    return counts


def _collect_model_rows(
    *,
    model_order: list[str],
    labels: dict[str, str],
    results: dict[str, minizinc_benchmark.BenchmarkResult],
) -> list[list[str]]:
    rows: list[list[str]] = []
    for key in model_order:
        result = results[key]
        all_runs = [r for inst in result.instances for r in result.runs_by_instance.get(inst, [])]
        counts = _status_counts(all_runs)
        total = len(all_runs)
        sat = counts[minizinc_benchmark.SolveStatus.OPTIMAL] + counts[minizinc_benchmark.SolveStatus.FEASIBLE]
        sat_pct = (100.0 * sat / total) if total else 0.0
        opt_pct = (100.0 * counts[minizinc_benchmark.SolveStatus.OPTIMAL] / total) if total else 0.0
        rows.append(
            [
                _display_model_name(key, labels),
                str(total),
                str(counts[minizinc_benchmark.SolveStatus.OPTIMAL]),
                str(counts[minizinc_benchmark.SolveStatus.FEASIBLE]),
                str(sat),
                str(counts[minizinc_benchmark.SolveStatus.TIMEOUT]),
                str(counts[minizinc_benchmark.SolveStatus.ERROR]),
                f"{sat_pct:.1f}",
                f"{opt_pct:.1f}",
                _format_float(_mean([r.compile_time_s for r in all_runs])),
                _format_float(_mean([r.solve_time_s for r in all_runs])),
            ]
        )
    return rows


def _all_benchmarks_done(state: dict[str, Any]) -> bool:
    model_order = state.get("model_order", [])
    benchmarks = state.get("benchmarks", {})
    return bool(model_order) and all(benchmarks.get(key) is not None for key in model_order)


def _build_pair_report(
    *,
    left_key: str,
    right_key: str,
    left_result: minizinc_benchmark.BenchmarkResult,
    right_result: minizinc_benchmark.BenchmarkResult,
) -> dict[str, Any]:
    left_runs = _flatten_runs(left_result)
    right_runs = _flatten_runs(right_result)
    keys_left = set(left_runs.keys())
    keys_right = set(right_runs.keys())
    shared_keys = sorted(keys_left & keys_right)

    transitions = {
        row.value: {col.value: 0 for col in STATUS_ORDER}
        for row in STATUS_ORDER
    }

    score_modes = [
        minizinc_benchmark.ScoreMode.MINIZINC_SOFT,
        minizinc_benchmark.ScoreMode.MINIZINC,
        minizinc_benchmark.ScoreMode.MINIZINC_AREA,
    ]
    scores = {mode.value: {"left": 0.0, "right": 0.0} for mode in score_modes}

    shared_sat_keys: list[tuple[str, int]] = []
    shared_opt_keys: list[tuple[str, int]] = []

    for key in shared_keys:
        left_run = left_runs[key]
        right_run = right_runs[key]
        transitions[left_run.status.value][right_run.status.value] += 1

        timeout = max(float(left_result.timeout_s), float(right_result.timeout_s))
        for mode in score_modes:
            cmp = minizinc_benchmark.compare_run_results(
                left_run,
                right_run,
                objective_sense=left_result.objective_sense,
                timeout_s=timeout,
                score_mode=mode,
            )
            scores[mode.value]["left"] += float(cmp.incumbent_score)
            scores[mode.value]["right"] += float(cmp.new_score)

        if left_run.status in SAT_STATUSES and right_run.status in SAT_STATUSES:
            shared_sat_keys.append(key)
        if (
            left_run.status == minizinc_benchmark.SolveStatus.OPTIMAL
            and right_run.status == minizinc_benchmark.SolveStatus.OPTIMAL
        ):
            shared_opt_keys.append(key)

    sat_left_obj = [
        left_runs[key].objective_value
        for key in shared_sat_keys
        if left_runs[key].objective_value is not None and right_runs[key].objective_value is not None
    ]
    sat_right_obj = [
        right_runs[key].objective_value
        for key in shared_sat_keys
        if left_runs[key].objective_value is not None and right_runs[key].objective_value is not None
    ]
    sat_missing_objective = len(shared_sat_keys) - len(sat_left_obj)

    opt_left_solve = [left_runs[key].solve_time_s for key in shared_opt_keys]
    opt_right_solve = [right_runs[key].solve_time_s for key in shared_opt_keys]

    return {
        "left_key": left_key,
        "right_key": right_key,
        "shared_pairs": len(shared_keys),
        "left_only_pairs": len(keys_left - keys_right),
        "right_only_pairs": len(keys_right - keys_left),
        "transitions": transitions,
        "scores": scores,
        "shared_sat_pairs": len(shared_sat_keys),
        "shared_opt_pairs": len(shared_opt_keys),
        "sat_missing_objective_pairs": sat_missing_objective,
        "sat_geomean_left": _geomean([float(v) for v in sat_left_obj]),
        "sat_geomean_right": _geomean([float(v) for v in sat_right_obj]),
        "opt_geomean_solve_left": _geomean(opt_left_solve),
        "opt_geomean_solve_right": _geomean(opt_right_solve),
    }


def _print_final_report(state: dict[str, Any]) -> None:
    model_order: list[str] = state["model_order"]
    labels: dict[str, str] = state.get("model_labels", {})
    results = {
        key: minizinc_benchmark.BenchmarkResult.from_dict(state["benchmarks"][key])
        for key in model_order
    }

    print()
    print("=" * 88)
    print("MINIZINC BENCHMARK REPORT")
    print("=" * 88)
    print(
        "Config: "
        f"solver={state['args']['minizinc_solver']}, "
        f"timeout_s={state['args']['benchmark_timeout']}, "
        f"runs_per_instance={state['args']['benchmark_runs_per_instance']}, "
        f"parallelism={state['args']['benchmark_parallelism']}, "
        f"use_slurm={state['args'].get('use_slurm', False)}, "
        f"objective_sense={state['args']['objective_sense']}"
    )
    print(f"Data dir: {state['args']['minizinc_data_dir']}")
    print()

    model_rows = _collect_model_rows(model_order=model_order, labels=labels, results=results)
    print("MODEL STATUS SUMMARY")
    print(
        _render_table(
            [
                "model",
                "runs",
                "OPT",
                "FEAS",
                "SAT",
                "TIMEOUT",
                "ERROR",
                "SAT_%",
                "OPT_%",
                "compile_avg_s",
                "solve_avg_s",
            ],
            model_rows,
        )
    )

    if len(model_order) == 2:
        left_key = model_order[0]
        right_key = model_order[1]
        pair = _build_pair_report(
            left_key=left_key,
            right_key=right_key,
            left_result=results[left_key],
            right_result=results[right_key],
        )
        left_name = _display_model_name(left_key, labels)
        right_name = _display_model_name(right_key, labels)

        print()
        print("PAIRWISE SUMMARY")

        headers = ["left_model", "right_model", "paired_runs", "left_only", "right_only"]
        row = [
            left_name,
            right_name,
            str(pair["shared_pairs"]),
            str(pair["left_only_pairs"]),
            str(pair["right_only_pairs"]),
        ]

        for mode_name, s_dict in pair["scores"].items():
            headers.extend([f"{mode_name.upper()}_left", f"{mode_name.upper()}_right"])
            row.extend([f"{s_dict['left']:.3f}", f"{s_dict['right']:.3f}"])

        print(_render_table(headers, [row]))

        print()
        print("STATE TRANSITION MATRIX (rows=left model, cols=right model)")
        matrix_rows = []
        for row_status in STATUS_ORDER:
            row = [row_status.value]
            for col_status in STATUS_ORDER:
                row.append(str(pair["transitions"][row_status.value][col_status.value]))
            matrix_rows.append(row)
        print(
            _render_table(
                ["left\\right"] + [s.value for s in STATUS_ORDER],
                matrix_rows,
            )
        )

        print()
        print("SHARED FILTERED GEOMEANS")
        print(
            _render_table(
                ["metric", "pairs_used", left_name, right_name, "notes"],
                [
                    [
                        "Both SAT: objective geomean",
                        str(pair["shared_sat_pairs"] - pair["sat_missing_objective_pairs"]),
                        _format_float(pair["sat_geomean_left"]),
                        _format_float(pair["sat_geomean_right"]),
                        (
                            f"missing objective in {pair['sat_missing_objective_pairs']} SAT pair(s)"
                            if pair["sat_missing_objective_pairs"]
                            else "-"
                        ),
                    ],
                    [
                        "Both OPT: solve-time geomean (s)",
                        str(pair["shared_opt_pairs"]),
                        _format_float(pair["opt_geomean_solve_left"]),
                        _format_float(pair["opt_geomean_solve_right"]),
                        "-",
                    ],
                ],
            )
        )

    print("=" * 88)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Resumable benchmark runner for one or two MiniZinc models. "
            "If the output JSON already contains complete results, no new benchmarking is run."
        )
    )
    parser.add_argument(
        "mzn_files",
        nargs="*",
        type=Path,
        help="One or two MiniZinc model files (.mzn).",
    )
    parser.add_argument(
        "--output-file",
        type=str,
        default=DEFAULT_OUTPUT_FILE_TEMPLATE,
        help=(
            "Output JSON file path. Supports {YYYY-MM-DD} and {HH-MM-SS}. "
            f"(default: {DEFAULT_OUTPUT_FILE_TEMPLATE})"
        ),
    )
    parser.add_argument(
        "--log-file",
        type=str,
        default=None,
        help="Optional log file path. Defaults to --output-file with .json replaced by .log.jsonl.",
    )
    parser.add_argument("--minizinc-data-dir", type=Path, default=DEFAULT_MINIZINC_DATA_DIR)
    parser.add_argument("--minizinc-solver", type=str, default=DEFAULT_MINIZINC_SOLVER)
    parser.add_argument("--benchmark-timeout", type=float, default=DEFAULT_BENCHMARK_TIMEOUT_S)
    parser.add_argument("--benchmark-runs-per-instance", type=int, default=DEFAULT_BENCHMARK_RUNS_PER_INSTANCE)
    parser.add_argument("--benchmark-parallelism", type=int, default=None)
    parser.add_argument(
        "--use-slurm",
        action="store_true",
        default=False,
        help="Run MiniZinc benchmarks via Slurm/submitit (one job per (instance, run_id)).",
    )
    parser.add_argument(
        "--objective-sense",
        choices=[s.value for s in minizinc_benchmark.ObjectiveSense],
        default=minizinc_benchmark.ObjectiveSense.MIN.value,
    )
    parser.add_argument("--verbose", action="store_true", default=False)
    return parser.parse_args()


def _build_new_state(args: argparse.Namespace, dt: datetime) -> dict[str, Any]:
    if not (1 <= len(args.mzn_files) <= 2):
        raise SystemExit("ERROR: Provide one or two .mzn files.")
    if not args.minizinc_data_dir.exists():
        raise SystemExit(f"ERROR: DZN directory not found: {args.minizinc_data_dir}")
    for p in args.mzn_files:
        if not p.exists():
            raise SystemExit(f"ERROR: MZN file not found: {p}")

    model_order = [_model_key(p) for p in args.mzn_files]
    model_labels = {_model_key(p): str(p) for p in args.mzn_files}

    return {
        "created_at": dt.isoformat(),
        "updated_at": dt.isoformat(),
        "completed_at": None,
        "args": {
            "minizinc_data_dir": str(args.minizinc_data_dir),
            "minizinc_solver": args.minizinc_solver,
            "benchmark_timeout": args.benchmark_timeout,
            "benchmark_runs_per_instance": args.benchmark_runs_per_instance,
            "benchmark_parallelism": args.benchmark_parallelism,
            "use_slurm": bool(args.use_slurm),
            "objective_sense": args.objective_sense,
        },
        "model_order": model_order,
        "model_labels": model_labels,
        "benchmarks": {key: None for key in model_order},
        "model_runs": {
            key: {"status": "pending", "started_at": None, "finished_at": None, "error": None}
            for key in model_order
        },
    }


def _load_or_init_state(args: argparse.Namespace, out_file: Path, dt: datetime) -> dict[str, Any]:
    if out_file.exists():
        state = _load_json(out_file)
        if args.mzn_files:
            provided = [_model_key(p) for p in args.mzn_files]
            actual = state.get("model_order", [])
            if len(actual) != len(args.mzn_files):
                raise SystemExit(
                    "ERROR: Number of provided mzn_files does not match existing output file model_order.\n"
                    f"  model_order_len={len(actual)}\n"
                    f"  provided_len={len(args.mzn_files)}"
                )
            if provided != actual:
                log.warning(
                    "Provided mzn_files do not match existing output file model_order; "
                    "assuming positional mapping (1st↔1st, 2nd↔2nd) and continuing.",
                    model_order=actual,
                    provided_mzn_files=[str(p) for p in args.mzn_files],
                )
        try:
            state_args = state.get("args") or {}
            requested_use_slurm = bool(args.use_slurm)
            existing_use_slurm = bool(state_args.get("use_slurm", False))
            if requested_use_slurm and not existing_use_slurm:
                state_args["use_slurm"] = True
                state["args"] = state_args
                state["updated_at"] = dt.isoformat()
                _atomic_save_json(out_file, state)
                log.info("Enabled use_slurm on resume", use_slurm=True, output_file=str(out_file))
            elif "use_slurm" not in state_args:
                state_args["use_slurm"] = requested_use_slurm
                state["args"] = state_args
                state["updated_at"] = dt.isoformat()
                _atomic_save_json(out_file, state)
                log.info(
                    "Initialized missing use_slurm on resume",
                    use_slurm=bool(state_args["use_slurm"]),
                    output_file=str(out_file),
                )
        except Exception as exc:  # noqa: BLE001
            log.exception("Failed to update use_slurm on resume", error=str(exc), output_file=str(out_file))
        return state
    state = _build_new_state(args, dt)
    _atomic_save_json(out_file, state)
    return state


def _benchmark_remaining(
    state: dict[str, Any],
    out_file: Path,
    *,
    mzn_files_by_key: dict[str, Path] | None = None,
) -> None:
    run_args = state["args"]
    objective_sense = minizinc_benchmark.ObjectiveSense(run_args["objective_sense"])
    for model_key in state["model_order"]:
        if state["benchmarks"].get(model_key) is not None:
            continue

        mzn_file = (mzn_files_by_key or {}).get(model_key, Path(model_key))
        model_label = state.get("model_labels", {}).get(model_key, model_key)
        state["model_runs"][model_key]["status"] = "running"
        state["model_runs"][model_key]["started_at"] = datetime.now().isoformat()
        state["model_runs"][model_key]["error"] = None
        state["updated_at"] = datetime.now().isoformat()
        _atomic_save_json(out_file, state)

        if not mzn_file.exists():
            raise SystemExit(
                "ERROR: MZN file not found for benchmarking.\n"
                f"  model_key={model_key}\n"
                f"  mapped_mzn_file={mzn_file}"
            )

        log.info("Benchmarking model", mzn_file=str(mzn_file), model_label=model_label, model_key=model_key)
        try:
            result = minizinc_benchmark.benchmark_mzn_file(
                mzn_file=mzn_file,
                solver=str(run_args["minizinc_solver"]),
                timeout_s=float(run_args["benchmark_timeout"]),
                runs_per_instance=int(run_args["benchmark_runs_per_instance"]),
                dzn_dir=Path(run_args["minizinc_data_dir"]),
                parallelism=run_args.get("benchmark_parallelism"),
                objective_sense=objective_sense,
                use_slurm=bool(run_args.get("use_slurm", False)),
            )
        except Exception as exc:  # noqa: BLE001
            state["model_runs"][model_key]["status"] = "error"
            state["model_runs"][model_key]["error"] = str(exc)
            state["model_runs"][model_key]["finished_at"] = datetime.now().isoformat()
            state["updated_at"] = datetime.now().isoformat()
            _atomic_save_json(out_file, state)
            log.exception("Model benchmark failed", mzn_file=model_label, error=str(exc))
            raise

        state["benchmarks"][model_key] = result.to_dict()
        state["model_runs"][model_key]["status"] = "done"
        state["model_runs"][model_key]["finished_at"] = datetime.now().isoformat()
        state["updated_at"] = datetime.now().isoformat()
        _atomic_save_json(out_file, state)
        log.info("Model benchmark complete", mzn_file=model_label)

    if _all_benchmarks_done(state):
        state["completed_at"] = datetime.now().isoformat()
        state["updated_at"] = state["completed_at"]
        _atomic_save_json(out_file, state)


def main() -> None:
    args = _parse_args()
    dt = datetime.now()
    out_file = _render_path_template(args.output_file, dt)
    log_file = (
        _render_path_template(args.log_file, dt)
        if args.log_file
        else _derive_log_file_from_output(out_file)
    )
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
        log_file=str(log_file),
    )

    state = _load_or_init_state(args, out_file, dt)
    mzn_files_by_key: dict[str, Path] | None = None
    if args.mzn_files:
        model_order = list(state.get("model_order", []))
        if len(model_order) != len(args.mzn_files):
            raise SystemExit(
                "ERROR: Number of provided mzn_files does not match existing output file model_order.\n"
                f"  model_order_len={len(model_order)}\n"
                f"  provided_len={len(args.mzn_files)}"
            )
        mzn_files_by_key = {key: p for key, p in zip(model_order, args.mzn_files, strict=True)}

        # Use the provided file paths as display labels (useful when resuming a JSON created elsewhere).
        labels = state.get("model_labels") or {}
        for key, p in mzn_files_by_key.items():
            labels[key] = str(p)
        state["model_labels"] = labels
    if _all_benchmarks_done(state):
        log.info("All model benchmarks already complete; printing report only", output_file=str(out_file))
        _print_final_report(state)
        return

    _benchmark_remaining(state, out_file, mzn_files_by_key=mzn_files_by_key)
    final_state = _load_json(out_file)
    if _all_benchmarks_done(final_state):
        _print_final_report(final_state)
    else:
        log.warning("Run ended with incomplete benchmarks", output_file=str(out_file))


if __name__ == "__main__":
    main()
