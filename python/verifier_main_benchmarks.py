"""
Benchmark LLM-based Lean theorem proving across multiple models and files.
"""
import argparse
import json
import logging
import os
import random
import signal
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, asdict, field
from pathlib import Path

import matplotlib
import numpy as np  # noqa: WPS433
from matplotlib.colors import LinearSegmentedColormap  # noqa: WPS433
from matplotlib.ticker import PercentFormatter  # noqa: WPS433
import psutil
import seaborn as sns  # noqa: WPS433
from scipy.stats import binomtest

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: WPS433

from . import mzn_compiler
from . import verifier_lean
from . import verifier_llm
from .helpers_logging import setup_logging, get_logger, thread_log_to_file

DEFAULT_MODE = "lean"
DEFAULT_NUM_RUNS = 1

DEFAULT_MODELS = [
    {"model_name": "gpt-oss-120b", "llm_model_name": "openrouter/openai/gpt-oss-120b", "reasoning_effort": "high", "max_turns": 5, "display_name": "gpt-oss-120b"},
    #{"model_name": "gpt-oss-20b", "llm_model_name": "openrouter/openai/gpt-oss-20b", "reasoning_effort": "high", "max_turns": 5, "display_name": "gpt-oss-20b"},
    {"model_name": "deepseek-v3.2", "llm_model_name": "openrouter/deepseek/deepseek-v3.2", "reasoning_effort": "high", "max_turns": 5, "display_name": "DeepSeek-V3.2"},
    {"model_name": "deepseek-prover-v2-orig_prompt_cot", "llm_model_name": "novita/deepseek/deepseek-prover-v2-671b", "reasoning_effort": "high", "max_turns": 5, "display_name": "DeepSeek-Prover-V2"},
    #{"model_name": "gemini-2.5-flash-lite", "llm_model_name": "gemini/gemini-2.5-flash-lite", "reasoning_effort": "high", "max_turns": 5},
    #{"model_name": "glm-4.6", "llm_model_name": "openrouter/z-ai/glm-4.6", "reasoning_effort": "high", "max_turns": 5, "display_name": "GLM-4.6"},
    #{"model_name": "glm-4.7", "llm_model_name": "openrouter/z-ai/glm-4.7", "reasoning_effort": "high", "max_turns": 5, "display_name": "GLM-4.7"},
    #{"model_name": "kimi-k2-thinking", "llm_model_name": "openrouter/moonshotai/kimi-k2-thinking", "reasoning_effort": "high", "max_turns": 5, "display_name": "Kimi K2 Thinking"},
    {"model_name": "gpt-5-mini", "llm_model_name": "openai/gpt-5-mini", "reasoning_effort": "high", "max_turns": 5, "display_name": "GPT-5 mini"},
    {"model_name": "claude-4.5-haiku", "llm_model_name": "anthropic/claude-haiku-4-5-20251001", "reasoning_effort": "high", "max_turns": 5, "display_name": "Claude Haiku 4.5"},
    {"model_name": "gemini-3-flash-preview", "llm_model_name": "gemini/gemini-3-flash-preview", "reasoning_effort": "high", "max_turns": 5, "display_name": "Gemini 3 Flash (Preview)"},
    #{"model_name": "deepseek-prover-v2-orig_prompt", "llm_model_name": "novita/deepseek/deepseek-prover-v2-671b", "reasoning_effort": None, "max_turns": 5, "display_name": "DeepSeek-Prover-V2 (no CoT)"},
    #{"model_name": "deepseek-prover-v2-orig_prompt_cot-pass_at_5", "llm_model_name": "novita/deepseek/deepseek-prover-v2-671b", "reasoning_effort": "high", "max_turns": 5, "display_name": "DeepSeek-Prover-V2 (CoT) Pass@5"},
    #{"model_name": "deepseek-prover-v2-orig_prompt_cot-pass_at_16", "llm_model_name": "novita/deepseek/deepseek-prover-v2-671b", "reasoning_effort": "high", "max_turns": 10, "display_name": "DeepSeek-Prover-V2 (CoT) Pass@16"},
]


PDF_OUT_NAME = "paper_benchmarks/llm_comparison.pdf"  # None disables plot export
SVG_FILL_GRADIENT = True
SVG_X_AXIS_LOG = False
SVG_Y_MAX_PERFECT = False

CUSTOM_COST_LLM_MODEL_NAME = "novita/deepseek/deepseek-prover-v2-671b"
CUSTOM_COST_INPUT_USD_PER_MTOK = 0.7
CUSTOM_COST_OUTPUT_USD_PER_MTOK = 2.5

DEFAULT_MAX_CONCURRENT_RUNS = 30
DEFAULT_OUTPUT_ONLY_MODE = False

REPORT_ABS_SUCCESS_RATE = True
VERIFIER_FIGURE_WIDTH_IN = 11.0 * 0.7
VERIFIER_FIGURE_HEIGHT_IN = VERIFIER_FIGURE_WIDTH_IN * (5.4 / 9.0)
PLOT_LABEL_SIZE_PT = 14
PLOT_TICK_SIZE_PT = 12


@dataclass
class RunResult:
    file: str
    model_name: str
    llm_model_name: str
    reasoning_effort: str
    max_turns: int
    run_id: int
    success: bool
    total_cost_ct: float
    turns_needed: int


@dataclass
class RunDatabase:
    lean_codes: dict = field(default_factory=dict)  # file -> lean_code
    runs: list = field(default_factory=list)  # list of RunResult dicts


# ============================================================================
# CLI Parsing
# ============================================================================
def parse_models(models_str: str) -> list[dict]:
    """Parse model configs from a string.

    Supported formats (space-separated):
      - "model"
      - "model:effort"
      - "model:effort:max_turns"
      - "model:max_turns"  (effort defaults to "medium")
      - "private=model[:effort][:max_turns]"  (private name used for stats)
    """
    result = []
    for part in models_str.split():
        private_name = None
        if "=" in part:
            private_name, part = part.split("=", 1)
            if not private_name:
                raise ValueError(f"Invalid model spec '{part}': empty private name before '='")
            if not part:
                raise ValueError(f"Invalid model spec '{private_name}=': missing model name after '='")

        max_turns = 3
        effort = "medium"

        if ":" in part:
            maybe_left, maybe_right = part.rsplit(":", 1)
            try:
                max_turns = int(maybe_right)
                part = maybe_left
            except ValueError:
                pass

        if ":" in part:
            model_name, effort = part.rsplit(":", 1)
        else:
            model_name = part

        if max_turns <= 0:
            raise ValueError(f"Invalid max_turns={max_turns} for model '{model_name}'")

        llm_model_name = model_name
        stats_name = private_name or model_name
        result.append(
            {
                "model_name": stats_name,
                "llm_model_name": llm_model_name,
                "reasoning_effort": effort,
                "max_turns": max_turns,
            }
        )
    return result


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Benchmark LLM-based Lean theorem proving")
    p.add_argument("in_dir", type=Path, help="Input directory containing .lean or .mzn files")
    p.add_argument("out_dir", type=Path, help="Output directory for runs.json and logs")
    p.add_argument("--mode", choices=["mzn", "lean"], default=DEFAULT_MODE)
    p.add_argument("--num-runs", type=int, default=DEFAULT_NUM_RUNS)
    p.add_argument(
        "--models",
        type=str,
        default=None,
        help='Format: "model[:effort][:max_turns] private=model[:effort][:max_turns] ..."',
    )
    p.add_argument("--max-concurrent-runs", type=int, default=DEFAULT_MAX_CONCURRENT_RUNS)
    p.add_argument(
        "--output-only",
        action="store_true",
        default=DEFAULT_OUTPUT_ONLY_MODE,
        help="Only print results from the existing database; do not run new benchmarks.",
    )
    p.add_argument(
        "--prove-non-redundant",
        action="store_true",
        default=False,
        help="In mzn mode, pass --prove-non-redundant to the mzn->lean compiler to invert the proven statement.",
    )

    args = p.parse_args()
    if args.models:
        try:
            args.models = parse_models(args.models)
        except ValueError as e:
            p.error(str(e))
    else:
        args.models = DEFAULT_MODELS
    return args


# ============================================================================
# Database I/O
# ============================================================================
def load_database(db_path: Path) -> RunDatabase:
    if not db_path.exists():
        return RunDatabase()
    data = json.loads(db_path.read_text())
    return RunDatabase(
        lean_codes=data.get("lean_codes", {}),
        runs=data.get("runs", [])
    )


def save_database(db: RunDatabase, db_path: Path):
    """Atomic save: tmp -> rename old -> rename tmp."""
    data = {"lean_codes": db.lean_codes, "runs": db.runs}
    tmp_path = db_path.with_suffix('.json.tmp')
    old_path = db_path.with_suffix('.json.old')

    tmp_path.write_text(json.dumps(data, indent=2))
    if db_path.exists():
        db_path.rename(old_path)
    tmp_path.rename(db_path)


# ============================================================================
# File Discovery & Preprocessing
# ============================================================================
def discover_files(in_dir: Path, mode: str) -> list[Path]:
    if mode == "mzn":
        return sorted(f for f in in_dir.rglob("*.mzn") if f.is_file())
    return sorted(f for f in list(in_dir.rglob("*.lean")) + list(in_dir.rglob("*.Lean")) if f.is_file())


def preprocess_files(files: list[Path], in_dir: Path, mode: str, db: RunDatabase,
                     prove_non_redundant: bool = False) -> dict[str, str]:
    """Compile/validate files, return file_key -> lean_code. Exits on error."""
    lean_codes = dict(db.lean_codes)
    to_process = [f for f in files if str(f.relative_to(in_dir)) not in lean_codes]

    if not to_process:
        print(f"All {len(files)} files already preprocessed.")
        return lean_codes

    print(f"Preprocessing {len(to_process)} files...")
    mzn_compiler.ensure_compiled()

    def process_one(f: Path) -> tuple[str, str]:
        key = str(f.relative_to(in_dir))
        if mode == "mzn":
            result = mzn_compiler.mzn_to_lean(f, validate_lean=False, prove_non_redundant=prove_non_redundant)
            if not result.success:
                raise RuntimeError(f"Compile failed for {key}: {result.compiler_stderr[:500]}")
            lean_code = result.lean_code
        else:
            lean_code = f.read_text()

        vr = verifier_lean.verify_lean_proof(lean_code, fill_line_info=False)
        if vr.return_code != 0:
            raise RuntimeError(f"Lean validation failed for {key}: {vr.lean_stderr[:500]}")
        return key, lean_code

    max_workers = psutil.cpu_count(logical=True) or 4
    with ThreadPoolExecutor(max_workers=max_workers) as ex:
        futures = {ex.submit(process_one, f): f for f in to_process}
        for fut in as_completed(futures):
            try:
                key, code = fut.result()
                lean_codes[key] = code
                print(f"  ✓ {key}")
            except Exception as e:
                print(f"  ✗ Error: {e}", file=sys.stderr)
                sys.exit(1)

    return lean_codes


# ============================================================================
# Run Execution
# ============================================================================
def run_key(file: str, model: str, effort: str, max_turns: int, run_id: int) -> tuple:
    return (file, model, effort, max_turns, run_id)


def existing_keys(db: RunDatabase) -> set[tuple]:
    return {
        run_key(r["file"], r["model_name"], r["reasoning_effort"], r.get("max_turns", 3), r["run_id"])
        for r in db.runs
    }


def execute_run(lean_code: str, file_key: str, model_name: str, effort: str,
                llm_model_name: str, run_id: int, max_turns: int, log_path: Path) -> dict:
    """Execute a single proof run with logging to the specified file."""
    log = get_logger()

    with thread_log_to_file(log_path):
        log.info(
            "Starting run",
            file=file_key,
            model=model_name,
            llm_model=llm_model_name,
            effort=effort,
            max_turns=max_turns,
            run_id=run_id,
        )

        try:
            result = verifier_llm.prove_lean_code(
                lean_code, llm_model_name, max_turns=max_turns, reasoning_setting=effort
            )
            run_result = RunResult(
                file=file_key,
                model_name=model_name,
                llm_model_name=llm_model_name,
                reasoning_effort=effort,
                max_turns=max_turns,
                run_id=run_id,
                success=result.success,
                total_cost_ct=result.total_cost_ct,
                turns_needed=result.turns_needed,
            )
            log.info(
                "Run complete",
                success=result.success,
                turns_needed=result.turns_needed,
                cost_ct=result.total_cost_ct,
            )
        except Exception as e:
            log.error("Exception during run", error=str(e), exc_info=True)
            run_result = RunResult(
                file=file_key,
                model_name=model_name,
                llm_model_name=llm_model_name,
                reasoning_effort=effort,
                max_turns=max_turns,
                run_id=run_id,
                success=False,
                total_cost_ct=0.0,
                turns_needed=-1,
            )

    return asdict(run_result)


# ============================================================================
# Output Tables
# ============================================================================
def wilson_ci(k: int, n: int, conf: float = 0.95) -> tuple[float, float]:
    if n == 0:
        return (0.0, 0.0)
    ci = binomtest(k, n).proportion_ci(confidence_level=conf, method='wilson')
    return (ci.low, ci.high)


def model_key(m: dict) -> str:
    return f"{m['model_name']}:{m['reasoning_effort']}:{m.get('max_turns', 3)}"

def model_label(m: dict) -> str:
    """Short label for tables.

    If a private model name is used (model_name != llm_model_name), prefer it as-is.
    Otherwise keep the historical compact formatting.
    """
    display_name = m.get("display_name")
    if display_name:
        return str(display_name)

    name = m["model_name"]
    llm_name = m.get("llm_model_name", name)
    if llm_name != name:
        return name
    base = name.split("/")[-1] if "/" in name else name
    effort = m["reasoning_effort"]
    max_turns = m.get("max_turns", 3)
    return f"{base}:{effort}:t{max_turns}"


def build_data_map(db: RunDatabase, files: list[str], models: list[dict]) -> dict:
    """Returns {file: {model_key: [run_dicts]}}."""
    data = {f: {model_key(m): [] for m in models} for f in files}
    for r in db.runs:
        mk = f"{r['model_name']}:{r['reasoning_effort']}:{r.get('max_turns', 3)}"
        if r["file"] in data and mk in data[r["file"]]:
            data[r["file"]][mk].append(r)
    return data


def _run_log_path(logs_dir: Path, run: dict) -> Path:
    model_name = run["model_name"].replace("/", "__")
    effort = run["reasoning_effort"]
    max_turns = run.get("max_turns", 3)
    run_id = run["run_id"]
    return logs_dir / run["file"] / f"{model_name}-{effort}-t{max_turns}-{run_id}.log"


def _load_step_usages_from_log(log_path: Path) -> list[dict]:
    if not log_path.exists():
        return []

    step_usage_by_turn: dict[int, dict] = {}
    with log_path.open(encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                payload = json.loads(line)
            except json.JSONDecodeError:
                continue

            event = payload.get("event")
            if not isinstance(event, str) or not (
                event.startswith("Received response from model (cost:")
                or event.startswith("Received response from DeepSeek-Prover (cost:")
            ):
                continue

            turn = payload.get("turn")
            llm_usage = payload.get("llm_usage")
            if not isinstance(turn, int) or not isinstance(llm_usage, dict):
                continue
            step_usage_by_turn[turn] = llm_usage

    return [step_usage_by_turn[turn] for turn in sorted(step_usage_by_turn)]


def _usage_cost_ct(llm_usage: dict, *, llm_model_name: str | None = None) -> float | None:
    if llm_model_name == CUSTOM_COST_LLM_MODEL_NAME:
        input_tokens = llm_usage.get("input_tokens")
        output_tokens = llm_usage.get("output_tokens")
        if input_tokens is None and output_tokens is None:
            return None
        input_ct = float(input_tokens or 0) * (CUSTOM_COST_INPUT_USD_PER_MTOK * 100.0) / 1_000_000.0
        output_ct = float(output_tokens or 0) * (CUSTOM_COST_OUTPUT_USD_PER_MTOK * 100.0) / 1_000_000.0
        return input_ct + output_ct

    cost_ct = llm_usage.get("cost_ct")
    return None if cost_ct is None else float(cost_ct)


def _load_step_costs_from_log(log_path: Path, *, llm_model_name: str | None = None) -> list[float]:
    usages = _load_step_usages_from_log(log_path)
    if not usages:
        return []
    return [
        cost_ct
        for usage in usages
        for cost_ct in [_usage_cost_ct(usage, llm_model_name=llm_model_name)]
        if cost_ct is not None
    ]


def _run_cost_ct(
    run: dict,
    logs_dir: Path | None,
    cost_cache: dict[tuple, float],
    backfill_state: dict[str, bool] | None = None,
) -> float:
    run_id = run_key(
        run["file"],
        run["model_name"],
        run["reasoning_effort"],
        run.get("max_turns", 3),
        run["run_id"],
    )
    if run_id in cost_cache:
        return cost_cache[run_id]

    llm_model_name = run.get("llm_model_name")
    if logs_dir is not None:
        step_costs = _load_step_costs_from_log(_run_log_path(logs_dir, run), llm_model_name=llm_model_name)
        if step_costs:
            cost_cache[run_id] = sum(step_costs)
            if ("total_cost_ct" not in run or run.get("total_cost_ct") is None) and backfill_state is not None:
                run["total_cost_ct"] = cost_cache[run_id]
                backfill_state["dirty"] = True
            return cost_cache[run_id]

    cost_cache[run_id] = float(run.get("total_cost_ct", 0.0))
    return cost_cache[run_id]


def _run_step_costs(
    run: dict,
    logs_dir: Path | None,
    step_cost_cache: dict[tuple, list[float]],
    cost_cache: dict[tuple, float],
    backfill_state: dict[str, bool] | None = None,
) -> list[float]:
    run_id = run_key(
        run["file"],
        run["model_name"],
        run["reasoning_effort"],
        run.get("max_turns", 3),
        run["run_id"],
    )
    if run_id in step_cost_cache:
        return step_cost_cache[run_id]

    step_costs: list[float] = []
    if logs_dir is not None:
        step_costs = _load_step_costs_from_log(
            _run_log_path(logs_dir, run),
            llm_model_name=run.get("llm_model_name"),
        )
    if not step_costs:
        total_cost_ct = _run_cost_ct(run, logs_dir, cost_cache, backfill_state)
        approx_turns = run.get("turns_needed", -1) if run.get("success") else run.get("max_turns", 3)
        approx_turns = max(int(approx_turns or 0), 1)
        if total_cost_ct > 0.0:
            step_costs = [total_cost_ct / approx_turns] * approx_turns

    step_cost_cache[run_id] = step_costs
    return step_costs


def _run_success_under_turn_budget(run: dict, turn_budget: int) -> bool:
    return bool(run.get("success")) and int(run.get("turns_needed", -1)) != -1 and int(run.get("turns_needed", 10**9)) <= turn_budget


def _run_cost_under_turn_budget(
    run: dict,
    turn_budget: int,
    logs_dir: Path | None,
    step_cost_cache: dict[tuple, list[float]],
    cost_cache: dict[tuple, float],
    backfill_state: dict[str, bool] | None = None,
) -> float:
    step_costs = _run_step_costs(run, logs_dir, step_cost_cache, cost_cache, backfill_state)
    if step_costs:
        return sum(step_costs[:max(0, turn_budget)])
    if turn_budget >= int(run.get("max_turns", 3)):
        return _run_cost_ct(run, logs_dir, cost_cache, backfill_state)
    total_cost_ct = _run_cost_ct(run, logs_dir, cost_cache, backfill_state)
    max_turns = max(int(run.get("max_turns", 3)), 1)
    return total_cost_ct * float(turn_budget) / float(max_turns)


def _collect_summary_points(
    data: dict[str, dict[str, list[dict]]],
    model_keys: list[str],
    labels_by_mk: dict[str, str],
    logs_dir: Path | None,
    abs_total_runs: int | None,
) -> list[dict]:
    points = []
    cost_cache: dict[tuple, float] = {}
    perfect_success_value = float(abs_total_runs or 0) if REPORT_ABS_SUCCESS_RATE else 1.0
    for mk in model_keys:
        per_instance_costs = []
        per_instance_success_rates = []
        total_successes = 0
        for per_model_runs in data.values():
            runs = per_model_runs.get(mk, [])
            if not runs:
                continue
            per_instance_costs.append(sum(_run_cost_ct(r, logs_dir, cost_cache) for r in runs) / len(runs))
            per_instance_success_rates.append(sum(bool(r.get("success")) for r in runs) / len(runs))
            total_successes += _success_counts(runs)[0]

        if not per_instance_costs:
            continue
        success_fraction = (
            (float(total_successes) / perfect_success_value)
            if REPORT_ABS_SUCCESS_RATE and perfect_success_value > 0
            else sum(per_instance_success_rates) / len(per_instance_success_rates)
        )
        points.append(
            {
                "label": labels_by_mk.get(mk, mk),
                "avg_cost_ct": sum(per_instance_costs) / len(per_instance_costs),
                "success_value": float(total_successes) if REPORT_ABS_SUCCESS_RATE else success_fraction,
                "success_fraction": success_fraction,
            }
        )
    return points


def _collect_turn_budget_points(
    data: dict[str, dict[str, list[dict]]],
    model_keys: list[str],
    labels_by_mk: dict[str, str],
    logs_dir: Path | None,
    abs_total_runs: int | None,
) -> list[dict]:
    points = []
    cost_cache: dict[tuple, float] = {}
    step_cost_cache: dict[tuple, list[float]] = {}
    perfect_success_value = float(abs_total_runs or 0) if REPORT_ABS_SUCCESS_RATE else 1.0

    for mk in model_keys:
        model_runs = [r for per_model_runs in data.values() for r in per_model_runs.get(mk, [])]
        if not model_runs:
            continue
        model_max_turn = max(int(r.get("max_turns", 3)) for r in model_runs)
        for turn_budget in range(1, model_max_turn + 1):
            per_instance_costs = []
            per_instance_success_rates = []
            total_successes = 0
            for per_model_runs in data.values():
                runs = per_model_runs.get(mk, [])
                if not runs:
                    continue
                per_instance_costs.append(
                    sum(
                        _run_cost_under_turn_budget(r, turn_budget, logs_dir, step_cost_cache, cost_cache)
                        for r in runs
                    ) / len(runs)
                )
                solved = sum(_run_success_under_turn_budget(r, turn_budget) for r in runs)
                per_instance_success_rates.append(float(solved) / len(runs))
                total_successes += solved

            success_fraction = (
                (float(total_successes) / perfect_success_value)
                if REPORT_ABS_SUCCESS_RATE and perfect_success_value > 0
                else sum(per_instance_success_rates) / len(per_instance_success_rates)
            )
            points.append(
                {
                    "model_key": mk,
                    "label": labels_by_mk.get(mk, mk),
                    "turn_budget": turn_budget,
                    "max_turns": model_max_turn,
                    "is_final": turn_budget == model_max_turn,
                    "avg_cost_ct": sum(per_instance_costs) / len(per_instance_costs),
                    "success_value": float(total_successes) if REPORT_ABS_SUCCESS_RATE else success_fraction,
                    "success_fraction": success_fraction,
                }
            )

    return points


def _add_cost_success_gradient(
    ax,
    *,
    xlim: tuple[float, float],
    ylim: tuple[float, float],
    svg_x_axis_log: bool,
    report_abs_success_rate: bool,
    perfect_success_value: float,
    reference_points: list[dict],
    centers_to_edges,
    alpha: float = 0.6,
) -> None:
    gradient_size = 256
    if svg_x_axis_log:
        xx = np.geomspace(xlim[0], xlim[1], gradient_size, dtype=float)
    else:
        xx = np.linspace(xlim[0], xlim[1], gradient_size, dtype=float)
    yy = np.linspace(ylim[0], ylim[1], gradient_size, dtype=float)
    grid_x, grid_y = np.meshgrid(xx, yy)
    success_floor = max(1e-3, (1e-3 * perfect_success_value) if report_abs_success_rate and perfect_success_value > 0 else 1e-3)
    grid_success_fraction = (
        grid_y / perfect_success_value
        if report_abs_success_rate and perfect_success_value > 0
        else grid_y
    )
    cost_per_success = grid_x / np.maximum(grid_success_fraction, 1e-3)
    score = np.log1p(cost_per_success)
    point_scores = [
        np.log1p(max(p["avg_cost_ct"], success_floor) / max(p["success_fraction"], 1e-3))
        for p in reference_points
    ]
    vmin = min(point_scores)
    vmax = max(point_scores)
    if vmax <= vmin:
        vmax = vmin + 1.0
    cmap = LinearSegmentedColormap.from_list(
        "cost_success_bg_shared",
        ["#cfe8cf", "#f7f7f7", "#efcaca"],
    )
    ax.pcolormesh(
        centers_to_edges(xx, log_scale=svg_x_axis_log),
        centers_to_edges(yy, log_scale=False),
        score,
        cmap=cmap,
        vmin=vmin,
        vmax=vmax,
        alpha=alpha,
        shading="auto",
        edgecolors="none",
        linewidth=0.0,
        antialiased=False,
        rasterized=True,
        zorder=0,
    )


def _success_counts(runs: list[dict]) -> tuple[int, int]:
    return sum(bool(r.get("success")) for r in runs), len(runs)


def _validate_abs_reporting(data: dict[str, dict[str, list[dict]]], model_keys: list[str]) -> int:
    """Return common total runs per model or raise on inconsistent coverage."""
    if not model_keys:
        return 0

    ref_mk = model_keys[0]
    ref_counts = {file_key: len(per_model_runs.get(ref_mk, [])) for file_key, per_model_runs in data.items()}
    for mk in model_keys[1:]:
        cur_counts = {file_key: len(per_model_runs.get(mk, [])) for file_key, per_model_runs in data.items()}
        if cur_counts != ref_counts:
            for file_key in sorted(data):
                expected = ref_counts.get(file_key, 0)
                actual = cur_counts.get(file_key, 0)
                if expected != actual:
                    raise SystemExit(
                        "ERROR: REPORT_ABS_SUCCESS_RATE requires identical instance coverage and run counts "
                        f"across models, but found mismatch for instance '{file_key}': "
                        f"{ref_mk} has {expected} runs, {mk} has {actual} runs."
                    )
            raise SystemExit(
                "ERROR: REPORT_ABS_SUCCESS_RATE requires identical instance coverage and run counts across models."
            )
    return sum(ref_counts.values())


def _format_success_cell(runs: list[dict]) -> str:
    k, n = _success_counts(runs)
    if REPORT_ABS_SUCCESS_RATE:
        return f"{k}/{n}" if n else "-"
    return f"{(k / n):.2f}" if n else "-"


def _format_success_ci_cell(runs: list[dict]) -> str:
    k, n = _success_counts(runs)
    if n == 0:
        return "-"
    lo, hi = wilson_ci(k, n)
    if REPORT_ABS_SUCCESS_RATE:
        return f"{k}/{n} [{lo * n:.1f},{hi * n:.1f}]"
    return f"{k / n:.2f} [{lo:.2f},{hi:.2f}]"


def _latex_escape(text: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(ch, ch) for ch in text)


def _latex_turn_success_cell(solved: int, total: int) -> str:
    if total <= 0:
        return "-"
    if REPORT_ABS_SUCCESS_RATE:
        return str(solved)
    return f"{100.0 * solved / total:.1f}\\%"


def _latex_avg_attempt_cost_usd(
    runs: list[dict],
    logs_dir: Path | None,
    cost_cache: dict[tuple, float],
) -> str:
    if not runs:
        return "-"
    avg_cost_ct = sum(_run_cost_ct(r, logs_dir, cost_cache) for r in runs) / len(runs)
    return f"{avg_cost_ct / 100.0:.4f}"


def _latex_table_turn_summary(
    mks: list[str],
    labels_by_mk: dict[str, str],
    model_runs: dict[str, list[dict]],
    max_turn: int,
    logs_dir: Path | None,
) -> str:
    col_spec = "l" + ("c" * max_turn) + "c"
    cost_cache: dict[tuple, float] = {}
    lines: list[str] = []
    lines.append("\\begin{table}[t]")
    lines.append("\\centering")
    lines.append(f"\\begin{{tabular}}{{{col_spec}}}")
    lines.append("\\toprule")
    headers = ["Model"] + [f"$\\leq${turn}" for turn in range(1, max_turn + 1)] + ["Avg. Attempt Cost (USD)"]
    lines.append(" & ".join(headers) + " \\\\")
    lines.append("\\midrule")
    for mk in mks:
        runs = model_runs[mk]
        total = len(runs)
        row = [f"\\texttt{{{_latex_escape(labels_by_mk[mk])}}}"]
        for turn in range(1, max_turn + 1):
            solved = sum(1 for r in runs if _run_success_under_turn_budget(r, turn))
            row.append(_latex_turn_success_cell(solved, total))
        row.append(_latex_avg_attempt_cost_usd(runs, logs_dir, cost_cache))
        lines.append(" & ".join(row) + " \\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    success_caption = "absolute proven-theorem counts" if REPORT_ABS_SUCCESS_RATE else "proven-theorem rates"
    lines.append(
        "\\caption{LLM Lean verifier benchmark summary by turn budget. "
        f"The turn columns report cumulative {success_caption}; "
        "Average Attempt Cost is the mean cost per proof attempt in USD.}"
    )
    lines.append("\\label{tbl:verifier-turn-summary}")
    lines.append("\\end{table}")
    return "\n".join(lines)


def _count_provable_theorems(data: dict[str, dict[str, list[dict]]], files: list[str], model_keys: list[str]) -> int:
    return sum(
        1
        for file_key in files
        if any(bool(run.get("success")) for mk in model_keys for run in data[file_key].get(mk, []))
    )


def _theorem_is_proven(data: dict[str, dict[str, list[dict]]], file_key: str, model_keys: list[str]) -> bool:
    return any(bool(run.get("success")) for mk in model_keys for run in data[file_key].get(mk, []))


def print_tables(db: RunDatabase, models: list[dict], files: list[str], logs_dir: Path | None = None) -> bool:
    data = build_data_map(db, files, models)
    mks = [model_key(m) for m in models]
    labels_by_mk = {model_key(m): model_label(m) for m in models}
    model_runs = {
        mk: [r for f in files for r in data[f][mk]]
        for mk in mks
    }
    abs_total_runs = _validate_abs_reporting(data, mks) if REPORT_ABS_SUCCESS_RATE else None
    max_turn = max((m.get("max_turns", 3) for m in models), default=0)
    provable_theorems = _count_provable_theorems(data, files, mks)

    fw = max(20, max((len(f) for f in files), default=20))
    cw = max(10, max((len(labels_by_mk[mk]) for mk in mks), default=10))

    def rate(runs):
        return sum(r["success"] for r in runs) / len(runs) if runs else None
    cost_cache: dict[tuple, float] = {}
    backfill_state = {"dirty": False}
    def mean_cost(runs):
        return (
            sum(_run_cost_ct(r, logs_dir, cost_cache, backfill_state) for r in runs) / len(runs)
            if runs else None
        )
    step_cost_cache: dict[tuple, list[float]] = {}
    def get_step_costs(run: dict) -> list[float]:
        return _run_step_costs(run, logs_dir, step_cost_cache, cost_cache, backfill_state)

    print()
    print(_latex_table_turn_summary(mks, labels_by_mk, model_runs, max_turn, logs_dir))

    # Table 1: Success Rate
    print("\n" + "=" * 80)
    print("SUCCESS" if REPORT_ABS_SUCCESS_RATE else "SUCCESS RATE")
    print("=" * 80)
    hdr = f"{'Instance':<{fw}}" + "".join(f" | {labels_by_mk[mk]:>{cw}}" for mk in mks)
    print(hdr)
    print("-" * len(hdr))
    for f in files:
        row = f"{f:<{fw}}"
        for mk in mks:
            cell = _format_success_cell(data[f][mk])
            row += f" | {cell:>{cw}}"
        print(row)

    # Table 2: Success Rate + Cost
    print("\n" + "=" * 80)
    print("SUCCESS + MEAN COST (ct)" if REPORT_ABS_SUCCESS_RATE else "SUCCESS RATE + MEAN COST (ct)")
    print("=" * 80)
    hdr = f"{'Instance':<{fw}}"
    for mk in mks:
        hdr += f" | {labels_by_mk[mk]:>{cw}} | {'cost':>7}"
    print(hdr)
    print("-" * len(hdr))
    for f in files:
        row = f"{f:<{fw}}"
        for mk in mks:
            runs = data[f][mk]
            c = mean_cost(runs)
            success_cell = _format_success_cell(runs)
            row += f" | {success_cell:>{cw}} | {c:>7.2f}" if c is not None and runs else f" | {'-':>{cw}} | {'-':>7}"
        print(row)

    # Table 3: Success Rate with 95% CI
    print("\n" + "=" * 80)
    print("SUCCESS [95% CI]" if REPORT_ABS_SUCCESS_RATE else "SUCCESS RATE [95% CI]")
    print("=" * 80)
    ciw = max(cw + 14, len(f"{abs_total_runs}/{abs_total_runs} [0.0,0.0]") if abs_total_runs is not None else cw + 14)
    hdr = f"{'Instance':<{fw}}" + "".join(f" | {labels_by_mk[mk]:>{ciw}}" for mk in mks)
    print(hdr)
    print("-" * len(hdr))
    for f in files:
        row = f"{f:<{fw}}"
        for mk in mks:
            cell = _format_success_ci_cell(data[f][mk])
            row += f" | {cell:>{ciw}}"
        print(row)
    print("=" * 80)

    # Table 4: Cumulative solved percentage by turn (transposed)
    print("\n" + "=" * 80)
    print("CUMULATIVE SOLVED BY TURN" + ("" if REPORT_ABS_SUCCESS_RATE else " (%)"))
    print("=" * 80)
    model_w = max(10, max((len(labels_by_mk[mk]) for mk in mks), default=10))
    turn_w = max(7, len(str(abs_total_runs or 0)))
    cost_w = 10
    step_cost_headers = [f"cost_step_{turn}" for turn in range(1, max_turn + 1)]
    step_cost_w = max([10] + [len(header) for header in step_cost_headers])
    hdr = (
        f"{'Model':<{model_w}}"
        + "".join(f" | {f't{turn}':>{turn_w}}" for turn in range(1, max_turn + 1))
        + f" | {'cost_ct':>{cost_w}}"
        + "".join(f" | {header:>{step_cost_w}}" for header in step_cost_headers)
    )
    print(hdr)
    print("-" * len(hdr))
    for mk in mks:
        row = f"{labels_by_mk[mk]:<{model_w}}"
        runs = model_runs[mk]
        run_step_costs = [get_step_costs(run) for run in runs]
        for turn in range(1, max_turn + 1):
            if not runs:
                row += f" | {'-':>{turn_w}}"
                continue
            solved = sum(
                1
                for r in runs
                if r.get("success")
                and r.get("turns_needed", -1) != -1
                and r.get("turns_needed", 10**9) <= turn
            )
            if REPORT_ABS_SUCCESS_RATE:
                row += f" | {solved:>{turn_w}d}"
            else:
                pct = 100.0 * solved / len(runs)
                row += f" | {pct:>{turn_w}.2f}"
        if runs:
            avg_cost_ct = sum(_run_cost_ct(r, logs_dir, cost_cache, backfill_state) for r in runs) / len(runs)
            row += f" | {avg_cost_ct:>{cost_w}.2f}"
        else:
            row += f" | {'-':>{cost_w}}"
        for step_idx in range(max_turn):
            step_costs = [
                step_cost_list[step_idx]
                for step_cost_list in run_step_costs
                if len(step_cost_list) > step_idx
            ]
            if step_costs:
                avg_step_cost_ct = sum(step_costs) / len(step_costs)
                row += f" | {avg_step_cost_ct:>{step_cost_w}.2f}"
            else:
                row += f" | {'-':>{step_cost_w}}"
        print(row)
    print("=" * 80)

    print("\n" + "=" * 80)
    print("THEOREM PROVABILITY")
    print("=" * 80)
    status_w = max(len("Proven"), len("yes"))
    hdr = f"{'Theorem':<{fw}} | {'Proven':>{status_w}}"
    print(hdr)
    print("-" * len(hdr))
    for file_key in sorted(files):
        proven = "yes" if _theorem_is_proven(data, file_key, mks) else "no"
        print(f"{file_key:<{fw}} | {proven:>{status_w}}")
    print("=" * 80)
    print(f"Theorems proven by at least one solver: {provable_theorems}/{len(files)}")

    if PDF_OUT_NAME:
        try:
            pdf_path = export_model_summary_svg(
                data,
                mks,
                labels_by_mk,
                Path(PDF_OUT_NAME),
                logs_dir=logs_dir,
                abs_total_runs=abs_total_runs,
            )
            if pdf_path is not None:
                print(f"\nWrote PDF summary to {pdf_path}")
            turns_pdf_path = export_model_turn_budget_svg(
                data,
                mks,
                labels_by_mk,
                Path(PDF_OUT_NAME).with_name("llm_comparison_turns.pdf"),
                logs_dir=logs_dir,
                abs_total_runs=abs_total_runs,
            )
            if turns_pdf_path is not None:
                print(f"Wrote PDF turn summary to {turns_pdf_path}")
        except Exception as exc:  # noqa: BLE001
            print(f"\nWarning: failed to write PDF summary to {PDF_OUT_NAME}: {exc}", file=sys.stderr)
    return backfill_state["dirty"]


def export_model_summary_svg(
    data: dict[str, dict[str, list[dict]]],
    model_keys: list[str],
    labels_by_mk: dict[str, str],
    out_path: Path,
    logs_dir: Path | None = None,
    abs_total_runs: int | None = None,
) -> Path | None:
    points = _collect_summary_points(data, model_keys, labels_by_mk, logs_dir, abs_total_runs)
    perfect_success_value = float(abs_total_runs or 0) if REPORT_ABS_SUCCESS_RATE else 1.0

    if not points:
        return None

    sns.set_theme(
        style="ticks",
        context="paper",
        rc={
            "font.size": PLOT_TICK_SIZE_PT,
            "axes.titlesize": PLOT_LABEL_SIZE_PT,
            "axes.labelsize": PLOT_LABEL_SIZE_PT,
            "xtick.labelsize": PLOT_TICK_SIZE_PT,
            "ytick.labelsize": PLOT_TICK_SIZE_PT,
            "legend.fontsize": PLOT_TICK_SIZE_PT,
        },
    )

    def padded_limits(values: list[float], *, clamp_zero: bool = False, clamp_one: bool = False) -> tuple[float, float]:
        lo = min(values)
        hi = max(values)
        span = hi - lo
        if span == 0:
            pad = max(abs(lo) * 0.15, 1.0 if not clamp_one else 0.05)
        else:
            pad = max(span * 0.12, 0.05 if clamp_one else 0.0)
        lower = lo - pad
        upper = hi + pad
        if clamp_zero:
            lower = max(0.0, lower)
        if clamp_one:
            lower = max(0.0, lower)
            upper = min(1.0, upper)
            if upper - lower < 0.1:
                center = 0.5 * (upper + lower)
                lower = max(0.0, center - 0.05)
                upper = min(1.0, center + 0.05)
        return lower, upper

    def centers_to_edges(values: np.ndarray, *, log_scale: bool = False) -> np.ndarray:
        if values.size == 1:
            center = float(values[0])
            if log_scale:
                low = max(center / 1.1, 1e-6)
                high = max(center * 1.1, low * 1.01)
                return np.asarray([low, high], dtype=float)
            return np.asarray([center - 0.5, center + 0.5], dtype=float)

        if log_scale:
            mids = np.sqrt(values[:-1] * values[1:])
            first = max((values[0] ** 2) / mids[0], 1e-6)
            last = max((values[-1] ** 2) / mids[-1], first * 1.01)
        else:
            mids = 0.5 * (values[:-1] + values[1:])
            first = values[0] - (mids[0] - values[0])
            last = values[-1] + (values[-1] - mids[-1])
        return np.concatenate(([first], mids, [last]))

    xs = [p["avg_cost_ct"] for p in points]
    ys = [p["success_value"] for p in points]
    if SVG_X_AXIS_LOG:
        positive_xs = [x for x in xs if x > 0.0]
        x_floor = max((min(positive_xs) * 0.8) if positive_xs else 1e-3, 1e-3)
        x_plot_values = [max(x, x_floor) for x in xs]
        xlim = padded_limits(x_plot_values, clamp_zero=False)
        xlim = (max(xlim[0], x_floor), xlim[1])
    else:
        x_floor = None
        x_plot_values = list(xs)
        xlim = padded_limits(xs, clamp_zero=True)
    if REPORT_ABS_SUCCESS_RATE:
        ylim = padded_limits(ys, clamp_zero=True, clamp_one=False)
        if SVG_Y_MAX_PERFECT and perfect_success_value > 0:
            ylim = (0.0, perfect_success_value)
    else:
        ylim = padded_limits(ys, clamp_zero=True, clamp_one=True)
        if SVG_Y_MAX_PERFECT:
            ylim = (0.0, 1.0)
    x_split = 0.5 * (min(x_plot_values) + max(x_plot_values))
    y_split = 0.5 * (min(ys) + max(ys))

    fig, ax = plt.subplots(figsize=(VERIFIER_FIGURE_WIDTH_IN, VERIFIER_FIGURE_HEIGHT_IN))
    dot_color = "#1f77b4"

    if SVG_FILL_GRADIENT:
        _add_cost_success_gradient(
            ax,
            xlim=xlim,
            ylim=ylim,
            svg_x_axis_log=SVG_X_AXIS_LOG,
            report_abs_success_rate=REPORT_ABS_SUCCESS_RATE,
            perfect_success_value=perfect_success_value,
            reference_points=points,
            centers_to_edges=centers_to_edges,
            alpha=0.6,
        )

    ax.axvline(x_split, color="#9aa0a6", linestyle="--", linewidth=1.0, alpha=0.9, zorder=1)
    ax.axhline(y_split, color="#9aa0a6", linestyle="--", linewidth=1.0, alpha=0.9, zorder=1)

    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    if SVG_X_AXIS_LOG:
        ax.set_xscale("log")

    def _candidate_offsets(label: str, x_ax: float, y_ax: float) -> list[tuple[int, int]]:
        force_left = "DeepSeek-Prover" in label
        horiz = -1 if (force_left or x_ax > 0.72) else 1
        vert = -1 if y_ax > 0.72 else 1
        if 0.25 <= y_ax <= 0.75:
            vert = -1 if y_ax >= 0.5 else 1
        if 0.25 <= x_ax <= 0.75 and 0.30 <= y_ax <= 0.70:
            vert = -1 if y_ax >= 0.5 else 1

        primary = (6 * horiz, 4 * vert)
        secondary = (6 * horiz, 0)
        tertiary = (0, 6 * vert)
        candidates = [
            primary,
            secondary,
            tertiary,
            (6 * horiz, -4 * vert),
            (8 * horiz, 2 * vert),
            (8 * horiz, -2 * vert),
            (-6 * horiz, 4 * vert),
            (-6 * horiz, -4 * vert),
            (0, -6 * vert),
        ]
        seen: set[tuple[int, int]] = set()
        ordered = []
        for offset in candidates:
            if offset not in seen:
                seen.add(offset)
                ordered.append(offset)
        return ordered

    def _overflow_penalty(bbox, bounds) -> float:
        return (
            max(0.0, bounds.x0 - bbox.x0)
            + max(0.0, bbox.x1 - bounds.x1)
            + max(0.0, bounds.y0 - bbox.y0)
            + max(0.0, bbox.y1 - bounds.y1)
        )

    def _overlap_area(a, b) -> float:
        x0 = max(a.x0, b.x0)
        y0 = max(a.y0, b.y0)
        x1 = min(a.x1, b.x1)
        y1 = min(a.y1, b.y1)
        if x1 <= x0 or y1 <= y0:
            return 0.0
        return float((x1 - x0) * (y1 - y0))

    fig.canvas.draw()
    renderer = fig.canvas.get_renderer()
    axes_bbox = ax.get_window_extent(renderer=renderer)
    placed_bboxes = []
    point_display_positions = []
    ordered_points = sorted(points, key=lambda item: (-len(item["label"]), -item["success_value"], item["avg_cost_ct"]))

    for idx, point in enumerate(ordered_points):
        x = max(point["avg_cost_ct"], x_floor) if x_floor is not None else point["avg_cost_ct"]
        y = point["success_value"]
        ax.scatter(x, y, s=95, color=dot_color, edgecolor="white", linewidth=0.9, zorder=3)
        point_display_positions.append(ax.transData.transform((x, y)))

        x_ax, y_ax = ax.transAxes.inverted().transform(ax.transData.transform((x, y)))
        best_choice = None
        best_score = None
        for dx, dy in _candidate_offsets(point["label"], float(x_ax), float(y_ax)):
            ann = ax.annotate(
                point["label"],
                (x, y),
                xytext=(dx, dy),
                textcoords="offset points",
                ha="left" if dx >= 0 else "right",
                va="bottom" if dy >= 0 else "top",
                fontsize=PLOT_TICK_SIZE_PT,
                color="#1f1f1f",
                zorder=4,
            )
            fig.canvas.draw()
            bbox = ann.get_window_extent(renderer=renderer).expanded(1.03, 1.12)
            overflow = _overflow_penalty(bbox, axes_bbox)
            overlap = sum(_overlap_area(bbox, other) for other in placed_bboxes)
            point_overlap = sum(
                1.0
                for px, py in point_display_positions[:-1]
                if bbox.x0 <= px <= bbox.x1 and bbox.y0 <= py <= bbox.y1
            )
            score = overflow * 1000.0 + overlap * 10.0 + point_overlap * 5000.0 + abs(dx) + abs(dy)
            ann.remove()
            if best_score is None or score < best_score:
                best_score = score
                best_choice = (dx, dy, bbox)

        assert best_choice is not None
        dx, dy, _bbox = best_choice
        ann = ax.annotate(
            point["label"],
            (x, y),
            xytext=(dx, dy),
            textcoords="offset points",
            ha="left" if dx >= 0 else "right",
            va="bottom" if dy >= 0 else "top",
            fontsize=PLOT_TICK_SIZE_PT,
            color="#1f1f1f",
            zorder=4,
        )
        fig.canvas.draw()
        placed_bboxes.append(ann.get_window_extent(renderer=renderer).expanded(1.03, 1.12))

    ax.set_xlabel("Average Cost per Proof Attempt (USD cents)")
    ax.set_ylabel("Proven Theorems" if REPORT_ABS_SUCCESS_RATE else "Success rate")
    if not REPORT_ABS_SUCCESS_RATE:
        ax.yaxis.set_major_formatter(PercentFormatter(xmax=1.0))
    ax.grid(True, which="major", linewidth=0.6, alpha=0.25)

    sns.despine(fig=fig)
    fig.tight_layout()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, format="pdf", bbox_inches="tight")
    plt.close(fig)
    return out_path


def export_model_turn_budget_svg(
    data: dict[str, dict[str, list[dict]]],
    model_keys: list[str],
    labels_by_mk: dict[str, str],
    out_path: Path,
    logs_dir: Path | None = None,
    abs_total_runs: int | None = None,
) -> Path | None:
    points = _collect_turn_budget_points(data, model_keys, labels_by_mk, logs_dir, abs_total_runs)
    if not points:
        return None
    gradient_reference_points = _collect_summary_points(data, model_keys, labels_by_mk, logs_dir, abs_total_runs)

    sns.set_theme(
        style="ticks",
        context="paper",
        rc={
            "font.size": PLOT_TICK_SIZE_PT,
            "axes.titlesize": PLOT_LABEL_SIZE_PT,
            "axes.labelsize": PLOT_LABEL_SIZE_PT,
            "xtick.labelsize": PLOT_TICK_SIZE_PT,
            "ytick.labelsize": PLOT_TICK_SIZE_PT,
            "legend.fontsize": PLOT_TICK_SIZE_PT,
        },
    )

    def padded_limits(values: list[float], *, clamp_zero: bool = False, clamp_one: bool = False) -> tuple[float, float]:
        lo = min(values)
        hi = max(values)
        span = hi - lo
        if span == 0:
            pad = max(abs(lo) * 0.15, 1.0 if not clamp_one else 0.05)
        else:
            pad = max(span * 0.12, 0.05 if clamp_one else 0.0)
        lower = lo - pad
        upper = hi + pad
        if clamp_zero:
            lower = max(0.0, lower)
        if clamp_one:
            lower = max(0.0, lower)
            upper = min(1.0, upper)
            if upper - lower < 0.1:
                center = 0.5 * (upper + lower)
                lower = max(0.0, center - 0.05)
                upper = min(1.0, center + 0.05)
        return lower, upper

    def centers_to_edges(values: np.ndarray, *, log_scale: bool = False) -> np.ndarray:
        if values.size == 1:
            center = float(values[0])
            if log_scale:
                low = max(center / 1.1, 1e-6)
                high = max(center * 1.1, low * 1.01)
                return np.asarray([low, high], dtype=float)
            return np.asarray([center - 0.5, center + 0.5], dtype=float)

        if log_scale:
            mids = np.sqrt(values[:-1] * values[1:])
            first = max((values[0] ** 2) / mids[0], 1e-6)
            last = max((values[-1] ** 2) / mids[-1], first * 1.01)
        else:
            mids = 0.5 * (values[:-1] + values[1:])
            first = values[0] - (mids[0] - values[0])
            last = values[-1] + (values[-1] - mids[-1])
        return np.concatenate(([first], mids, [last]))

    xs = [p["avg_cost_ct"] for p in gradient_reference_points]
    ys = [p["success_value"] for p in gradient_reference_points]
    if SVG_X_AXIS_LOG:
        positive_xs = [x for x in xs if x > 0.0]
        x_floor = max((min(positive_xs) * 0.8) if positive_xs else 1e-3, 1e-3)
        x_plot_values = [max(x, x_floor) for x in xs]
        xlim = padded_limits(x_plot_values, clamp_zero=False)
        xlim = (max(xlim[0], x_floor), xlim[1])
    else:
        x_floor = None
        xlim = padded_limits(xs, clamp_zero=True)

    perfect_success_value = float(abs_total_runs or 0) if REPORT_ABS_SUCCESS_RATE else 1.0
    if REPORT_ABS_SUCCESS_RATE:
        ylim = padded_limits(ys, clamp_zero=True, clamp_one=False)
        if SVG_Y_MAX_PERFECT and perfect_success_value > 0:
            ylim = (0.0, perfect_success_value)
    else:
        ylim = padded_limits(ys, clamp_zero=True, clamp_one=True)
        if SVG_Y_MAX_PERFECT:
            ylim = (0.0, 1.0)

    fig, ax = plt.subplots(figsize=(VERIFIER_FIGURE_WIDTH_IN, VERIFIER_FIGURE_HEIGHT_IN))
    dot_color = "#1f77b4"

    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    if SVG_X_AXIS_LOG:
        ax.set_xscale("log")

    if SVG_FILL_GRADIENT:
        _add_cost_success_gradient(
            ax,
            xlim=xlim,
            ylim=ylim,
            svg_x_axis_log=SVG_X_AXIS_LOG,
            report_abs_success_rate=REPORT_ABS_SUCCESS_RATE,
            perfect_success_value=perfect_success_value,
            reference_points=gradient_reference_points,
            centers_to_edges=centers_to_edges,
            alpha=0.6,
        )

    def _candidate_offsets(label: str, x_ax: float, y_ax: float) -> list[tuple[int, int]]:
        force_left = "DeepSeek-Prover" in label
        horiz = -1 if (force_left or x_ax > 0.72) else 1
        vert = -1 if y_ax > 0.72 else 1
        if 0.25 <= y_ax <= 0.75:
            vert = -1 if y_ax >= 0.5 else 1
        if 0.25 <= x_ax <= 0.75 and 0.30 <= y_ax <= 0.70:
            vert = -1 if y_ax >= 0.5 else 1
        candidates = [
            (6 * horiz, 4 * vert),
            (6 * horiz, 0),
            (0, 6 * vert),
            (6 * horiz, -4 * vert),
            (8 * horiz, 2 * vert),
            (8 * horiz, -2 * vert),
        ]
        seen: set[tuple[int, int]] = set()
        ordered = []
        for offset in candidates:
            if offset not in seen:
                seen.add(offset)
                ordered.append(offset)
        return ordered

    def _overflow_penalty(bbox, bounds) -> float:
        return (
            max(0.0, bounds.x0 - bbox.x0)
            + max(0.0, bbox.x1 - bounds.x1)
            + max(0.0, bounds.y0 - bbox.y0)
            + max(0.0, bbox.y1 - bounds.y1)
        )

    def _overlap_area(a, b) -> float:
        x0 = max(a.x0, b.x0)
        y0 = max(a.y0, b.y0)
        x1 = min(a.x1, b.x1)
        y1 = min(a.y1, b.y1)
        if x1 <= x0 or y1 <= y0:
            return 0.0
        return float((x1 - x0) * (y1 - y0))

    final_points = []
    for mk in model_keys:
        model_points = sorted((p for p in points if p["model_key"] == mk), key=lambda item: item["turn_budget"])
        if not model_points:
            continue
        xs_line = [max(p["avg_cost_ct"], x_floor) if x_floor is not None else p["avg_cost_ct"] for p in model_points]
        ys_line = [p["success_value"] for p in model_points]
        n_points = len(model_points)
        if n_points <= 1:
            dot_alphas = [0.95]
        else:
            dot_alphas = []
            for idx in range(n_points):
                if idx == n_points - 1:
                    dot_alphas.append(0.95)
                else:
                    frac = idx / max(n_points - 2, 1)
                    dot_alphas.append(0.25 + frac * (0.40 - 0.25))

        for idx in range(n_points - 1):
            seg_alpha = min(0.55, 0.05 + 0.95 * (0.8 * dot_alphas[idx] + 0.2 * dot_alphas[idx + 1]))
            ax.plot(
                xs_line[idx:idx + 2],
                ys_line[idx:idx + 2],
                color=dot_color,
                linewidth=1.8,
                alpha=seg_alpha,
                zorder=2,
            )

        for point, x, y, alpha in zip(model_points, xs_line, ys_line, dot_alphas):
            ax.scatter(
                x,
                y,
                s=70 if point["is_final"] else 42,
                color=dot_color,
                edgecolor="white",
                linewidth=0.8,
                alpha=alpha,
                zorder=3 if point["is_final"] else 2.5,
            )
        final_points.append((model_points[-1], xs_line[-1], ys_line[-1]))

    fig.canvas.draw()
    renderer = fig.canvas.get_renderer()
    axes_bbox = ax.get_window_extent(renderer=renderer)
    placed_bboxes = []
    for point, x, y in sorted(final_points, key=lambda item: (-len(item[0]["label"]), -item[2], item[1])):
        x_ax, y_ax = ax.transAxes.inverted().transform(ax.transData.transform((x, y)))
        best_choice = None
        best_score = None
        for dx, dy in _candidate_offsets(point["label"], float(x_ax), float(y_ax)):
            ann = ax.annotate(
                point["label"],
                (x, y),
                xytext=(dx, dy),
                textcoords="offset points",
                ha="left" if dx >= 0 else "right",
                va="bottom" if dy >= 0 else "top",
                fontsize=PLOT_TICK_SIZE_PT,
                color="#1f1f1f",
                zorder=4,
            )
            fig.canvas.draw()
            bbox = ann.get_window_extent(renderer=renderer).expanded(1.03, 1.12)
            overflow = _overflow_penalty(bbox, axes_bbox)
            overlap = sum(_overlap_area(bbox, other) for other in placed_bboxes)
            score = overflow * 1000.0 + overlap * 10.0 + abs(dx) + abs(dy)
            ann.remove()
            if best_score is None or score < best_score:
                best_score = score
                best_choice = (dx, dy)

        assert best_choice is not None
        dx, dy = best_choice
        ann = ax.annotate(
            point["label"],
            (x, y),
            xytext=(dx, dy),
            textcoords="offset points",
            ha="left" if dx >= 0 else "right",
            va="bottom" if dy >= 0 else "top",
            fontsize=PLOT_TICK_SIZE_PT,
            color="#1f1f1f",
            zorder=4,
        )
        fig.canvas.draw()
        placed_bboxes.append(ann.get_window_extent(renderer=renderer).expanded(1.03, 1.12))

    ax.set_xlabel("Average Cost per Proof Attempt (USD cents)")
    ax.set_ylabel("Proven Theorems" if REPORT_ABS_SUCCESS_RATE else "Success rate")
    if not REPORT_ABS_SUCCESS_RATE:
        ax.yaxis.set_major_formatter(PercentFormatter(xmax=1.0))
    ax.grid(True, which="major", linewidth=0.6, alpha=0.25)

    sns.despine(fig=fig)
    fig.tight_layout()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, format="pdf", bbox_inches="tight")
    plt.close(fig)
    return out_path


def file_keys_from_db(db: RunDatabase) -> list[str]:
    """Return sorted list of file keys found in the database."""
    files = set(db.lean_codes.keys())
    files.update(r["file"] for r in db.runs if "file" in r)
    return sorted(files)


# ============================================================================
# Shutdown Handling
# ============================================================================
_shutdown = threading.Event()
_force_shutdown = threading.Event()


def signal_handler(signum, frame):
    if _shutdown.is_set():
        print("\nForce shutdown. Exiting immediately.")
        _force_shutdown.set()
        os._exit(1)
    print("\nGraceful shutdown. Finishing active runs...")
    _shutdown.set()


# ============================================================================
# Main
# ============================================================================
def main():
    args = parse_args()

    out_path = args.out_dir
    db_path = out_path / "runs.json"
    logs_dir = out_path / "logs"

    # Setup logging with per-thread file support
    setup_logging(level=logging.INFO, enable_console=True, enable_thread_file_logging=True)
    log = get_logger()

    if args.output_only:
        if not db_path.exists():
            print(f"No runs database found at {db_path}")
            return

        db = load_database(db_path)
        if not db.runs:
            print(f"No runs stored in database {db_path}")
            return

        models = args.models
        if not models:
            print(f"No model entries found in database {db_path}")
            return

        file_keys = file_keys_from_db(db)
        if print_tables(db, models, file_keys, logs_dir=logs_dir):
            save_database(db, db_path)
        return

    out_path.mkdir(parents=True, exist_ok=True)
    db = load_database(db_path)

    files = discover_files(args.in_dir, args.mode)
    if not files:
        print(f"No {args.mode} files found in {args.in_dir}")
        return
    file_keys = [str(f.relative_to(args.in_dir)) for f in files]
    print(f"Found {len(files)} {args.mode} files")

    # Preprocessing
    lean_codes = preprocess_files(files, args.in_dir, args.mode, db,
                                  prove_non_redundant=args.prove_non_redundant)
    db.lean_codes = lean_codes
    save_database(db, db_path)

    # Determine pending tasks
    existing = existing_keys(db)
    tasks = [
        (fk, m["model_name"], m.get("llm_model_name", m["model_name"]), m["reasoning_effort"], m.get("max_turns", 3), rid)
        for fk in file_keys
        for m in args.models
        for rid in range(args.num_runs)
        if run_key(fk, m["model_name"], m["reasoning_effort"], m.get("max_turns", 3), rid) not in existing
    ]
    random.shuffle(tasks)

    total = len(file_keys) * len(args.models) * args.num_runs
    if not tasks:
        print(f"\nAll {total} runs complete.")
        if print_tables(db, args.models, file_keys, logs_dir=logs_dir):
            save_database(db, db_path)
        return

    print(f"\n{len(tasks)} runs pending (of {total} total)")

    signal.signal(signal.SIGINT, signal_handler)

    db_lock = threading.Lock()
    completed = 0

    def do_task(task):
        fk, model_name, llm_model_name, effort, max_turns, rid = task
        log_file = logs_dir / fk / f"{model_name.replace('/', '__')}-{effort}-t{max_turns}-{rid}.log"
        return execute_run(lean_codes[fk], fk, model_name, effort, llm_model_name, rid, max_turns, log_file)

    with ThreadPoolExecutor(max_workers=args.max_concurrent_runs) as executor:
        # Submit tasks with staggered startup to allow LLM input caches to fill
        futures = {}
        for i, task in enumerate(tasks):
            futures[executor.submit(do_task, task)] = task
            # 1s delay between submissions until all worker slots are active
            if i < args.max_concurrent_runs - 1:
                time.sleep(1)

        for future in as_completed(futures):
            if _shutdown.is_set():
                # Cancel pending futures, let running ones finish
                for f in futures:
                    f.cancel()
                break

            t = futures[future]
            try:
                result = future.result()
                with db_lock:
                    db.runs.append(result)
                    save_database(db, db_path)
                completed += 1
                s = "✓" if result["success"] else "✗"
                print(
                    f"[{completed}/{len(tasks)}] {s} {result['file']} | {result['model_name']} "
                    f"| {result['reasoning_effort']} | t{result.get('max_turns', 3)} | run {result['run_id']}"
                )
            except Exception as e:
                print(f"Error: {t} -> {e}", file=sys.stderr)

    print(f"\nCompleted {completed} runs.")
    if print_tables(db, args.models, file_keys, logs_dir=logs_dir):
        save_database(db, db_path)


if __name__ == "__main__":
    main()
