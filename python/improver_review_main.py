"""Review and display results from improver_main.py JSON output files."""

from __future__ import annotations

import argparse
import json
import math
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Callable


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _truncate(text: str, max_len: int) -> str:
    if len(text) <= max_len:
        return text
    return text[: max_len - 3] + "..."


def _format_cmp(cmp: dict[str, Any] | None) -> str:
    if cmp is None:
        return "      -/      -"

    # New format: MiniZinc-style Borda scores
    if "incumbent_score" in cmp or "new_score" in cmp:
        inc = float(cmp.get("incumbent_score") or 0.0)
        new = float(cmp.get("new_score") or 0.0)
        return f"{inc:6.1f}/{new:6.1f}"

    # Legacy format: win/tie counts
    inc = int(cmp.get("incumbent_wins", 0) or 0)
    new = int(cmp.get("new_wins", 0) or 0)
    tie = int(cmp.get("ties", 0) or 0)
    return f"{inc:>4}/{new:>4}/{tie:>4}"

def _format_p_value(p: Any, width: int = 8) -> str:
    try:
        f = float(p)
    except (TypeError, ValueError):
        return " " * width
    if not math.isfinite(f):
        return " " * width
    # Compact scientific format, right-aligned.
    s = f"{f:.3g}"
    return s.rjust(width)


def _outcome_symbol(outcome: str) -> str:
    symbols = {
        "SUCCESS": "[OK]",
        "BENCHMARK_FAIL": "[BF]",
        "BENCHMARK_ERROR": "[BE]",
        "PROOF_FAIL": "[PF]",
        "PROOF_ERROR": "[PE]",
        "UNKNOWN": "[??]",
    }
    return symbols.get(outcome, f"[{outcome[:2]}]")


def _bool_yn(val: bool | None) -> str:
    if val is None:
        return "-"
    return "Y" if val else "N"


def _calc_sat_opt_pct(benchmark: dict[str, Any] | None) -> tuple[float | None, float | None]:
    """Calculate %SAT and %OPT from benchmark results.

    Returns (sat_pct, opt_pct) where:
    - sat_pct = percentage of runs with FEASIBLE or OPTIMAL status
    - opt_pct = percentage of runs with OPTIMAL status
    """
    if benchmark is None:
        return None, None

    runs_by_instance = benchmark.get("runs_by_instance", {})
    if not runs_by_instance:
        return None, None

    total = 0
    sat_count = 0
    opt_count = 0

    for runs in runs_by_instance.values():
        for run in runs:
            total += 1
            status = run.get("status", "")
            if status in ("FEASIBLE", "OPTIMAL"):
                sat_count += 1
            if status == "OPTIMAL":
                opt_count += 1

    if total == 0:
        return None, None

    return (sat_count / total * 100, opt_count / total * 100)


def _format_pct(val: float | None) -> str:
    """Format percentage with one decimal, right-aligned for values up to 100.0%."""
    if val is None:
        return "    -"
    return f"{val:5.1f}"


def _get_original_baseline(state: dict[str, Any]) -> dict[str, Any] | None:
    """Get the original baseline benchmark from state.

    The first evaluation's incumbent_benchmark is the original baseline.
    Falls back to top-level incumbent_benchmark if no evaluations exist.
    """
    evaluations = state.get("evaluations", [])
    if evaluations:
        return evaluations[0].get("incumbent_benchmark")
    return state.get("incumbent_benchmark")


def _count_statuses(benchmark: dict[str, Any] | None) -> dict[str, int]:
    """Count runs by status in a benchmark result."""
    counts = {"OPTIMAL": 0, "FEASIBLE": 0, "TIMEOUT": 0, "ERROR": 0}
    if benchmark is None:
        return counts

    runs_by_instance = benchmark.get("runs_by_instance", {})
    for runs in runs_by_instance.values():
        for run in runs:
            status = run.get("status", "ERROR")
            if status in counts:
                counts[status] += 1
            else:
                counts["ERROR"] += 1
    return counts


def _flatten_runs(benchmark: dict[str, Any] | None) -> dict[tuple[str, int], dict[str, Any]]:
    """Flatten benchmark runs into a dict keyed by (instance, run_id)."""
    result: dict[tuple[str, int], dict[str, Any]] = {}
    if benchmark is None:
        return result

    runs_by_instance = benchmark.get("runs_by_instance", {})
    for instance, runs in runs_by_instance.items():
        for run in runs:
            key = (instance, run.get("run_id", 0))
            result[key] = run
    return result


def _as_finite_float(val: Any) -> float | None:
    try:
        f = float(val)
    except (TypeError, ValueError):
        return None
    if math.isfinite(f):
        return f
    return None


def _geomean_nonnegative(values: list[float]) -> float | None:
    """Geometric mean for nonnegative values (returns 0.0 if any value is 0)."""
    if not values:
        return None
    if any(v < 0.0 for v in values):
        return None
    if any(v == 0.0 for v in values):
        return 0.0
    return _geomean(values)


def _collect_step_candidate_benchmarks(evaluations: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Collect step candidate benchmarks (new_benchmark) from evaluations."""
    benchmarks: list[dict[str, Any]] = []
    for ev in evaluations:
        bm = ev.get("new_benchmark")
        if isinstance(bm, dict) and bm.get("runs_by_instance"):
            benchmarks.append(bm)
    return benchmarks


def _run_has_valid_opt_time(run: dict[str, Any]) -> bool:
    if run.get("status") != "OPTIMAL":
        return False
    t = _as_finite_float(run.get("solve_time_s"))
    return t is not None and t >= 0.0


def _run_has_valid_penalty(run: dict[str, Any]) -> bool:
    if run.get("status") not in ("OPTIMAL", "FEASIBLE"):
        return False
    p = _as_finite_float(run.get("objective_value"))
    return p is not None and p >= 0.0


def _benchmark_has_any_valid_run(
    benchmark: dict[str, Any] | None,
    predicate: Callable[[dict[str, Any]], bool],
) -> bool:
    if benchmark is None:
        return False
    runs_by_instance = benchmark.get("runs_by_instance", {})
    for runs in runs_by_instance.values():
        for run in runs:
            if predicate(run):
                return True
    return False


def _compute_consistent_run_keys_for_models(
    models: list[dict[str, Any]],
    predicate: Callable[[dict[str, Any]], bool],
) -> set[tuple[str, int]]:
    if not models:
        return set()

    flattened = [_flatten_runs(m) for m in models]
    key_sets = [set(fr.keys()) for fr in flattened]
    if not key_sets:
        return set()

    common_keys = set.intersection(*key_sets)
    if not common_keys:
        return set()

    consistent_keys: set[tuple[str, int]] = set()
    for key in common_keys:
        if all(predicate(fr.get(key, {})) for fr in flattened):
            consistent_keys.add(key)
    return consistent_keys


def _compute_consistent_run_keys(
    *,
    baseline: dict[str, Any] | None,
    candidates: list[dict[str, Any]],
) -> tuple[set[tuple[str, int]], set[tuple[str, int]]]:
    """Compute run keys that are consistent across baseline + all candidates.

    Returns (always_opt_keys, always_obj_satopt_keys):
    - always_opt_keys: keys where every model is OPTIMAL with finite solve_time_s >= 0
    - always_obj_satopt_keys: keys where every model has finite objective_value >= 0 and status in {OPTIMAL, FEASIBLE}
    """
    base_models: list[dict[str, Any]] = []
    if baseline is not None and baseline.get("runs_by_instance"):
        base_models.append(baseline)

    opt_models = base_models + [
        bm for bm in candidates if _benchmark_has_any_valid_run(bm, _run_has_valid_opt_time)
    ]
    obj_models = base_models + [
        bm for bm in candidates if _benchmark_has_any_valid_run(bm, _run_has_valid_penalty)
    ]

    return (
        _compute_consistent_run_keys_for_models(opt_models, _run_has_valid_opt_time),
        _compute_consistent_run_keys_for_models(obj_models, _run_has_valid_penalty),
    )


def _geomean_opt_time_on_keys(benchmark: dict[str, Any] | None, keys: set[tuple[str, int]]) -> float | None:
    if benchmark is None or not keys:
        return None
    runs = _flatten_runs(benchmark)
    times: list[float] = []
    for key in keys:
        run = runs.get(key)
        if not run:
            continue
        if run.get("status") != "OPTIMAL":
            continue
        t = _as_finite_float(run.get("solve_time_s"))
        if t is not None and t >= 0.0:
            times.append(t)
    return _geomean_nonnegative(times) if times else None


def _geomean_penalty_on_keys(benchmark: dict[str, Any] | None, keys: set[tuple[str, int]]) -> float | None:
    if benchmark is None or not keys:
        return None
    runs = _flatten_runs(benchmark)
    penalties: list[float] = []
    for key in keys:
        run = runs.get(key)
        if not run:
            continue
        if run.get("status") not in ("OPTIMAL", "FEASIBLE"):
            continue
        obj = run.get("objective_value")
        if obj is None:
            continue
        p = _as_finite_float(obj)
        if p is None:
            continue
        if p >= 0.0:
            penalties.append(p)
    return _geomean_nonnegative(penalties) if penalties else None


def _compare_benchmarks_to_baseline(
    baseline: dict[str, Any],
    new: dict[str, Any],
    objective_sense: str = "min",
) -> dict[str, Any]:
    """Compare new benchmark to baseline, returning detailed comparison stats.

    Returns dict with:
    - base_wins, new_wins, ties: win/lose/tie counts
    - opt_geomean_base, opt_geomean_new: geomean solve time for runs where both OPTIMAL
    - sat_geomean_base, sat_geomean_new: geomean objective for runs where both FEASIBLE (not OPTIMAL)
    - base_counts, new_counts: status counts for each benchmark
    """
    base_runs = _flatten_runs(baseline)
    new_runs = _flatten_runs(new)

    base_wins = 0
    new_wins = 0
    ties = 0

    # For geomean calculations
    opt_times_base: list[float] = []
    opt_times_new: list[float] = []
    sat_objs_base: list[float] = []
    sat_objs_new: list[float] = []

    # Match runs by (instance, run_id)
    common_keys = set(base_runs.keys()) & set(new_runs.keys())

    for key in common_keys:
        b_run = base_runs[key]
        n_run = new_runs[key]

        b_status = b_run.get("status", "ERROR")
        n_status = n_run.get("status", "ERROR")

        # Determine winner for this run
        winner = _compare_single_run(b_run, n_run, objective_sense)
        if winner == "base":
            base_wins += 1
        elif winner == "new":
            new_wins += 1
        else:
            ties += 1

        # Collect data for geomean calculations
        if b_status == "OPTIMAL" and n_status == "OPTIMAL":
            b_time = b_run.get("solve_time_s", 0.0)
            n_time = n_run.get("solve_time_s", 0.0)
            if b_time > 0 and n_time > 0:
                opt_times_base.append(b_time)
                opt_times_new.append(n_time)

        if b_status == "FEASIBLE" and n_status == "FEASIBLE":
            b_obj = b_run.get("objective_value")
            n_obj = n_run.get("objective_value")
            if b_obj is not None and n_obj is not None and b_obj > 0 and n_obj > 0:
                sat_objs_base.append(b_obj)
                sat_objs_new.append(n_obj)

    # Calculate geomeans
    opt_geomean_base = _geomean(opt_times_base) if opt_times_base else None
    opt_geomean_new = _geomean(opt_times_new) if opt_times_new else None
    sat_geomean_base = _geomean(sat_objs_base) if sat_objs_base else None
    sat_geomean_new = _geomean(sat_objs_new) if sat_objs_new else None

    return {
        "base_wins": base_wins,
        "new_wins": new_wins,
        "ties": ties,
        "total": len(common_keys),
        "opt_count": len(opt_times_base),
        "opt_geomean_base": opt_geomean_base,
        "opt_geomean_new": opt_geomean_new,
        "sat_count": len(sat_objs_base),
        "sat_geomean_base": sat_geomean_base,
        "sat_geomean_new": sat_geomean_new,
        "base_counts": _count_statuses(baseline),
        "new_counts": _count_statuses(new),
    }


def _compare_single_run(
    base_run: dict[str, Any],
    new_run: dict[str, Any],
    objective_sense: str,
) -> str:
    """Compare two runs, return 'base', 'new', or 'tie'."""

    def status_rank(status: str) -> int:
        if status == "OPTIMAL":
            return 3
        if status == "FEASIBLE":
            return 2
        return 1  # TIMEOUT or ERROR

    b_status = base_run.get("status", "ERROR")
    n_status = new_run.get("status", "ERROR")
    b_rank = status_rank(b_status)
    n_rank = status_rank(n_status)

    # Higher status rank wins
    if b_rank != n_rank:
        return "base" if b_rank > n_rank else "new"

    # Both timeout/error
    if b_rank == 1:
        return "tie"

    # Both FEASIBLE: compare objectives
    if b_rank == 2:
        b_obj = base_run.get("objective_value")
        n_obj = new_run.get("objective_value")
        if b_obj is None or n_obj is None:
            # Fall back to runtime
            b_time = base_run.get("solve_time_s", 0.0)
            n_time = new_run.get("solve_time_s", 0.0)
            if b_time == n_time:
                return "tie"
            return "base" if b_time < n_time else "new"
        if b_obj == n_obj:
            return "tie"
        if objective_sense == "min":
            return "base" if b_obj < n_obj else "new"
        return "base" if b_obj > n_obj else "new"

    # Both OPTIMAL: compare solve times
    b_time = base_run.get("solve_time_s", 0.0)
    n_time = new_run.get("solve_time_s", 0.0)
    if b_time == n_time:
        return "tie"
    return "base" if b_time < n_time else "new"


def _geomean(values: list[float]) -> float | None:
    """Calculate geometric mean of positive values."""
    if not values:
        return None
    # Use log-sum-exp for numerical stability
    log_sum = sum(math.log(v) for v in values if v > 0)
    return math.exp(log_sum / len(values))


def _format_geomean(val: float | None, width: int = 8) -> str:
    """Format geomean value with appropriate precision."""
    if val is None:
        return "-".rjust(width)
    if val >= 100:
        return f"{val:.1f}".rjust(width)
    if val >= 10:
        return f"{val:.2f}".rjust(width)
    return f"{val:.3f}".rjust(width)


def _format_status_counts(counts: dict[str, int], width: int = 4) -> str:
    """Format status counts as O/S/T/E."""
    o = counts.get("OPTIMAL", 0)
    s = counts.get("FEASIBLE", 0)
    t = counts.get("TIMEOUT", 0)
    e = counts.get("ERROR", 0)
    return f"{o:>{width}}/{s:>{width}}/{t:>{width}}/{e:>{width}}"


def print_constraints_table(evaluations: list[dict[str, Any]], state: dict[str, Any] | None = None) -> None:
    """Print overview table of all constraint evaluations."""
    if not evaluations:
        print("No evaluations found.")
        return

    baseline = _get_original_baseline(state) if state else None
    candidates = _collect_step_candidate_benchmarks(evaluations)
    always_opt_keys, always_obj_satopt_keys = _compute_consistent_run_keys(
        baseline=baseline,
        candidates=candidates,
    )
    opt_candidate_count = sum(1 for bm in candidates if _benchmark_has_any_valid_run(bm, _run_has_valid_opt_time))
    obj_candidate_count = sum(1 for bm in candidates if _benchmark_has_any_valid_run(bm, _run_has_valid_penalty))

    print("\n" + "=" * 100)
    print("CONSTRAINT EVALUATION OVERVIEW")
    print("=" * 100)
    print()
    print(
        "Geomean sets across initial incumbent + eligible step candidates: "
        f"GeoOptT uses {len(always_opt_keys)} instance/run-id pairs; "
        f"GeoPen uses {len(always_obj_satopt_keys)} instance/run-id pairs "
        f"(GeoOptT candidates={opt_candidate_count}/{len(candidates)}, "
        f"GeoPen candidates={obj_candidate_count}/{len(candidates)})"
    )
    print()

    # Header
    header = (
        f"{'#':>3}  "
        f"{'Outcome':6}  "
        f"{'BM':>3}  "
        f"{'PF':>3}  "
        f"{'Inc/New':>15}  "
        f"{'p':>8}  "
        f"{'Mode':>4}  "
        f"{'%SAT':>5}  "
        f"{'%OPT':>5}  "
        f"{'GeoOptT':>8}  "
        f"{'GeoPen':>8}  "
        f"{'Constraint Name':<40}"
    )
    print(header)
    print("-" * len(header))

    # Print baseline row first
    if baseline is not None:
        base_sat_pct, base_opt_pct = _calc_sat_opt_pct(baseline)
        base_geo_opt = _geomean_opt_time_on_keys(baseline, always_opt_keys)
        base_geo_pen = _geomean_penalty_on_keys(baseline, always_obj_satopt_keys)
        print(
            f"{'---':>3}  "
            f"{'':6}  "
            f"{'':>3}  "
            f"{'':>3}  "
            f"{'':>15}  "
            f"{'':>8}  "
            f"{'':>4}  "
            f"{_format_pct(base_sat_pct):>5}  "
            f"{_format_pct(base_opt_pct):>5}  "
            f"{_format_geomean(base_geo_opt, 8):>8}  "
            f"{_format_geomean(base_geo_pen, 8):>8}  "
            f"{'[BASELINE - Original Model]':<40}"
        )
        print("-" * len(header))

    for ev in evaluations:
        eval_id = ev.get("eval_id", "?")
        constraint = ev.get("constraint", {})
        name = constraint.get("name", "<unnamed>")
        outcome = ev.get("outcome", "UNKNOWN")
        accepted_by_benchmark = ev.get("accepted_by_benchmark")
        benchmark_cmp = ev.get("benchmark_comparison")
        benchmark_wilcoxon = ev.get("benchmark_wilcoxon") or {}
        p_value = benchmark_wilcoxon.get("p_value")
        score_mode = str(benchmark_wilcoxon.get("score_mode") or "")

        # Determine if proof passed
        proof = ev.get("proof")
        proof_passed: bool | None = None
        if proof is not None:
            waterfall = proof.get("waterfall")
            if waterfall is not None:
                proof_passed = waterfall.get("success", False)
            elif proof.get("compile_success") is False:
                proof_passed = False

        # Calculate %SAT and %OPT from new_benchmark (or incumbent_benchmark as fallback)
        benchmark = ev.get("new_benchmark") or ev.get("incumbent_benchmark")
        sat_pct, opt_pct = _calc_sat_opt_pct(benchmark)
        geo_opt = _geomean_opt_time_on_keys(benchmark, always_opt_keys)
        geo_pen = _geomean_penalty_on_keys(benchmark, always_obj_satopt_keys)

        cmp_str = _format_cmp(benchmark_cmp)
        bm_yn = _bool_yn(accepted_by_benchmark)
        pf_yn = _bool_yn(proof_passed)
        outcome_sym = _outcome_symbol(outcome)

        print(
            f"{eval_id:>3}  "
            f"{outcome_sym:6}  "
            f"{bm_yn:>3}  "
            f"{pf_yn:>3}  "
            f"{cmp_str:>15}  "
            f"{_format_p_value(p_value, 8)}  "
            f"{score_mode[:4]:>4}  "
            f"{_format_pct(sat_pct):>5}  "
            f"{_format_pct(opt_pct):>5}  "
            f"{_format_geomean(geo_opt, 8):>8}  "
            f"{_format_geomean(geo_pen, 8):>8}  "
            f"{_truncate(name, 40):<40}"
        )

    print()

    # Summary stats
    outcomes = [ev.get("outcome", "UNKNOWN") for ev in evaluations]
    outcome_counts = Counter(outcomes)
    print("Outcome Summary:")
    for outcome, count in sorted(outcome_counts.items()):
        print(f"  {outcome}: {count}")

    total_bm_pass = sum(1 for ev in evaluations if ev.get("accepted_by_benchmark"))
    total_success = sum(1 for ev in evaluations if ev.get("outcome") == "SUCCESS")
    print(f"\nBenchmark passed: {total_bm_pass}/{len(evaluations)}")
    print(f"Fully successful: {total_success}/{len(evaluations)}")


def print_proof_details_table(evaluations: list[dict[str, Any]]) -> None:
    """Print detailed proof attempt information."""
    # Filter to evaluations that have proof info
    proof_evals = [
        ev for ev in evaluations
        if ev.get("proof") is not None and ev.get("proof", {}).get("waterfall") is not None
    ]

    if not proof_evals:
        print("\nNo proof attempts recorded.")
        return

    print("\n" + "=" * 100)
    print("PROOF ATTEMPT DETAILS")
    print("=" * 100)
    print()

    # Collect all models used across all evaluations
    all_models: set[str] = set()
    for ev in proof_evals:
        waterfall = ev.get("proof", {}).get("waterfall", {})
        all_attempts = waterfall.get("all_attempts", {})
        all_models.update(all_attempts.keys())

    all_models_sorted = sorted(all_models)

    if not all_models_sorted:
        print("No model attempts found.")
        return

    # Create header
    model_headers = [_truncate(m.split("/")[-1], 15) for m in all_models_sorted]
    header = f"{'#':>3}  {'Outcome':6}  " + "  ".join(f"{h:>15}" for h in model_headers)
    print(header)
    print("-" * len(header))

    for ev in proof_evals:
        eval_id = ev.get("eval_id", "?")
        outcome = ev.get("outcome", "UNKNOWN")
        waterfall = ev.get("proof", {}).get("waterfall", {})
        all_attempts = waterfall.get("all_attempts", {})

        model_stats = []
        for model in all_models_sorted:
            attempts = all_attempts.get(model, [])
            if not attempts:
                model_stats.append("-")
            else:
                successes = sum(1 for a in attempts if a.get("success"))
                total = len(attempts)
                if successes > 0:
                    model_stats.append(f"{successes}/{total} OK")
                else:
                    model_stats.append(f"0/{total}")

        outcome_sym = _outcome_symbol(outcome)
        stats_str = "  ".join(f"{s:>15}" for s in model_stats)
        print(f"{eval_id:>3}  {outcome_sym:6}  {stats_str}")

    print()

    # Aggregate statistics
    print("Aggregate Proof Statistics by Model:")
    print("-" * 60)
    for model in all_models_sorted:
        total_attempts = 0
        total_successes = 0
        total_cost_ct = 0.0

        for ev in proof_evals:
            waterfall = ev.get("proof", {}).get("waterfall", {})
            all_attempts = waterfall.get("all_attempts", {})
            attempts = all_attempts.get(model, [])

            for a in attempts:
                total_attempts += 1
                if a.get("success"):
                    total_successes += 1
                total_cost_ct += a.get("total_cost_ct", 0.0)

        if total_attempts > 0:
            success_rate = total_successes / total_attempts * 100
            model_short = model.split("/")[-1]
            print(
                f"  {model_short:30}  "
                f"Attempts: {total_attempts:4}  "
                f"Success: {total_successes:3} ({success_rate:5.1f}%)  "
                f"Cost: ${total_cost_ct/100:.2f}"
            )


def print_constraint_details(evaluations: list[dict[str, Any]]) -> None:
    """Print detailed information about each constraint."""
    if not evaluations:
        return

    print("\n" + "=" * 100)
    print("CONSTRAINT DETAILS")
    print("=" * 100)

    for ev in evaluations:
        eval_id = ev.get("eval_id", "?")
        constraint = ev.get("constraint", {})
        name = constraint.get("name", "<unnamed>")
        description = constraint.get("description", "")
        code = constraint.get("code", "")
        outcome = ev.get("outcome", "UNKNOWN")

        print(f"\n--- Evaluation #{eval_id}: {name} ---")
        print(f"Outcome: {outcome}")
        if description:
            print(f"Description: {_truncate(description, 300)}")
        if code:
            print(f"Code: {_truncate(code, 300)}")

        # Benchmark info
        cmp = ev.get("benchmark_comparison")
        if cmp:
            total = cmp.get("total_compared", 0)
            if "incumbent_score" in cmp or "new_score" in cmp:
                inc_score = float(cmp.get("incumbent_score") or 0.0)
                new_score = float(cmp.get("new_score") or 0.0)
                print(f"Benchmark score: incumbent={inc_score:.3f}, new={new_score:.3f} (total={total})")
            else:
                inc = cmp.get("incumbent_wins", 0)
                new = cmp.get("new_wins", 0)
                tie = cmp.get("ties", 0)
                print(f"Benchmark: incumbent={inc}, new={new}, tie={tie} (total={total})")

        # Proof info
        proof = ev.get("proof")
        if proof:
            compile_ok = proof.get("compile_success")
            if compile_ok is False:
                print("Proof: Compilation failed")
                stderr = proof.get("compiler_stderr", "")
                if stderr:
                    print(f"  Error: {_truncate(stderr, 80)}")
            elif proof.get("waterfall"):
                wf = proof["waterfall"]
                success = wf.get("success", False)
                attempts = wf.get("attempts", 0)
                model_used = wf.get("model_used", "")
                if success:
                    print(f"Proof: SUCCESS with {model_used} ({attempts} total attempts)")
                else:
                    print(f"Proof: FAILED ({attempts} total attempts)")


def _is_proof_successful(ev: dict[str, Any]) -> bool:
    """Check if proof passed for this evaluation."""
    proof = ev.get("proof")
    if proof is None:
        return False
    waterfall = proof.get("waterfall")
    if waterfall is None:
        return False
    return waterfall.get("success", False)


def _is_evaluation_successful(ev: dict[str, Any]) -> bool:
    """Check if evaluation was fully successful (benchmark accepted + proof passed)."""
    return ev.get("accepted_by_benchmark", False) and _is_proof_successful(ev)


def _is_benchmark_pass_proof_fail(ev: dict[str, Any]) -> bool:
    """Check if evaluation passed benchmark but failed proof."""
    return ev.get("accepted_by_benchmark", False) and not _is_proof_successful(ev)


def _print_baseline_comparison_table(
    state: dict[str, Any],
    filter_fn: callable,
    title: str,
    empty_msg: str,
    footer_note: str | None = None,
) -> None:
    """Print table comparing filtered constraints to the original baseline."""
    evaluations = state.get("evaluations", [])
    baseline = _get_original_baseline(state)

    if baseline is None:
        print("\nNo baseline benchmark found.")
        return

    filtered_evals = [ev for ev in evaluations if filter_fn(ev)]

    if not filtered_evals:
        print(f"\n{empty_msg}")
        return

    args = state.get("args", {})
    objective_sense = args.get("objective_sense", "min")

    print("\n" + "=" * 140)
    print(title)
    print("=" * 140)
    print()

    header = (
        f"{'#':>3}  "
        f"{'Base/New/Tie':>14}  "
        f"{'OptT-Base':>9}  "
        f"{'OptT-New':>9}  "
        f"{'n':>4}  "
        f"{'SatO-Base':>9}  "
        f"{'SatO-New':>9}  "
        f"{'n':>4}  "
        f"{'Base O/S/T/E':>19}  "
        f"{'New O/S/T/E':>19}  "
        f"{'Name':<25}"
    )
    print(header)
    print("-" * len(header))

    for ev in filtered_evals:
        new_benchmark = ev.get("new_benchmark")
        if new_benchmark is None:
            continue

        cmp = _compare_benchmarks_to_baseline(baseline, new_benchmark, objective_sense)
        name = ev.get("constraint", {}).get("name", "<unnamed>")

        print(
            f"{ev.get('eval_id', '?'):>3}  "
            f"{cmp['base_wins']:>4}/{cmp['new_wins']:>4}/{cmp['ties']:>4}  "
            f"{_format_geomean(cmp['opt_geomean_base'], 9):>9}  "
            f"{_format_geomean(cmp['opt_geomean_new'], 9):>9}  "
            f"{cmp['opt_count']:>4}  "
            f"{_format_geomean(cmp['sat_geomean_base'], 9):>9}  "
            f"{_format_geomean(cmp['sat_geomean_new'], 9):>9}  "
            f"{cmp['sat_count']:>4}  "
            f"{_format_status_counts(cmp['base_counts'], 4):>19}  "
            f"{_format_status_counts(cmp['new_counts'], 4):>19}  "
            f"{_truncate(name, 25):<25}"
        )

    print()
    print("Legend:")
    print("  Base/New/Tie: Win counts comparing to original baseline (matching by instance+run_id)")
    print("  OptT-*: Geometric mean solve time (s) for runs where both are OPTIMAL")
    print("  SatO-*: Geometric mean objective for runs where both are FEASIBLE (not OPTIMAL)")
    print("  O/S/T/E: Count of OPTIMAL/FEASIBLE/TIMEOUT/ERROR runs")
    if footer_note:
        print(f"  Note: {footer_note}")


def print_baseline_comparison_table(state: dict[str, Any]) -> None:
    """Print table comparing successful constraints to the original baseline."""
    _print_baseline_comparison_table(
        state,
        filter_fn=_is_evaluation_successful,
        title="COMPARISON TO ORIGINAL BASELINE (Successful Constraints Only)",
        empty_msg="No successful constraint evaluations to compare against baseline.",
    )


def print_baseline_comparison_unproven_table(state: dict[str, Any]) -> None:
    """Print table comparing benchmark-passing but proof-failing constraints to baseline."""
    _print_baseline_comparison_table(
        state,
        filter_fn=_is_benchmark_pass_proof_fail,
        title="COMPARISON TO ORIGINAL BASELINE (Benchmark Pass, Proof Fail)",
        empty_msg="No benchmark-passing proof-failing constraints to compare against baseline.",
        footer_note="These constraints improved benchmarks but could not be formally proven",
    )


def print_sampling_info(state: dict[str, Any]) -> None:
    """Print information about sampling calls."""
    sampling_calls = state.get("sampling_calls", [])
    if not sampling_calls:
        return

    print("\n" + "=" * 100)
    print("SAMPLING CALLS")
    print("=" * 100)
    print()

    total_calls = len(sampling_calls)
    successful = sum(1 for c in sampling_calls if c.get("success"))
    failed = total_calls - successful

    print(f"Total sampling calls: {total_calls}")
    print(f"Successful: {successful}, Failed: {failed}")

    # Cost summary
    total_cost = 0.0
    for call in sampling_calls:
        usage = call.get("llm_usage", {})
        total_cost += usage.get("cost_ct", 0.0)

    if total_cost > 0:
        print(f"Total sampling cost: ${total_cost/100:.2f}")


def print_run_summary(state: dict[str, Any]) -> None:
    """Print high-level run summary."""
    args = state.get("args", {})

    print("\n" + "=" * 100)
    print("RUN SUMMARY")
    print("=" * 100)
    print()

    print(f"Created: {state.get('created_at', 'unknown')}")
    print(f"Updated: {state.get('updated_at', 'unknown')}")
    print()

    print("Configuration:")
    print(f"  MiniZinc model: {args.get('minizinc_model', 'unknown')}")
    print(f"  Solver: {args.get('minizinc_solver', 'unknown')}")
    print(f"  Sample model: {args.get('sample_model', 'unknown')}")
    print(f"  Target steps: {args.get('total_steps', 'unknown')}")
    print(f"  Cumulative: {args.get('cumulative', False)}")
    print(f"  Benchmark timeout: {args.get('benchmark_timeout', 'unknown')}s")
    print(f"  Benchmark runs/instance: {args.get('benchmark_runs_per_instance', 'unknown')}")

    # Waterfall config
    waterfall = args.get("verifier_waterfall", [])
    if waterfall:
        print("\n  Verifier waterfall:")
        for stage in waterfall:
            model = stage.get("model", "unknown")
            max_runs = stage.get("max_runs", 0)
            parallelism = stage.get("parallelism", 1)
            max_turns = stage.get("max_turns", 1)
            print(f"    {model}: max_runs={max_runs}, parallelism={parallelism}, max_turns={max_turns}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Review improver_main.py results"
    )
    parser.add_argument(
        "json_file",
        type=Path,
        help="Path to the JSON output file from improver_main.py",
    )
    parser.add_argument(
        "--details",
        action="store_true",
        help="Show detailed constraint information",
    )
    parser.add_argument(
        "--no-proof",
        action="store_true",
        help="Skip proof details table",
    )
    parser.add_argument(
        "--no-sampling",
        action="store_true",
        help="Skip sampling info",
    )
    args = parser.parse_args()

    if not args.json_file.exists():
        print(f"Error: File not found: {args.json_file}", file=sys.stderr)
        sys.exit(1)

    try:
        state = _load_json(args.json_file)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON: {e}", file=sys.stderr)
        sys.exit(1)

    print_run_summary(state)

    evaluations = state.get("evaluations", [])
    print_constraints_table(evaluations, state)

    print_baseline_comparison_table(state)
    print_baseline_comparison_unproven_table(state)

    if not args.no_proof:
        print_proof_details_table(evaluations)

    if not args.no_sampling:
        print_sampling_info(state)

    if args.details:
        print_constraint_details(evaluations)

    # Pending constraints
    pending = state.get("pending_constraints", [])
    if pending:
        print(f"\nPending constraints: {len(pending)}")


if __name__ == "__main__":
    main()
