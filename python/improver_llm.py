import litellm

from python import minizinc_benchmark
from . import helpers_llm_config

from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional
from pydantic import BaseModel
import structlog

log = structlog.get_logger()


class RedundantConstraint(BaseModel):
    name: str
    description: str
    code: str


class RedundantConstraintBatch(BaseModel):
    constraints: list[RedundantConstraint]


@dataclass
class PreviousConstraintAttempt:
    name: str
    description: str
    code: str
    outcome: str
    incumbent_benchmark: minizinc_benchmark.BenchmarkResult
    new_benchmark: minizinc_benchmark.BenchmarkResult


@dataclass
class ImproveResult:
    success: bool
    constraint_name: str
    constraint_description: str
    constraint_code: str
    error_message: str
    llm_usage: dict = field(default_factory=dict)


@dataclass
class ImproveBatchResult:
    success: bool
    constraints: list[ImproveResult]
    error_message: str
    llm_usage: dict = field(default_factory=dict)


SYSTEM_PROMPT = (Path(__file__).parent / "prompts" / "prompt_improver_system.txt").read_text()

PREVIOUS_ATTEMPTS_SECTION_TEMPLATE = """\n## Previous Constraint Attempts

Use this information to inform your next choice. Make sure to not repeat earlier attempts.
Be creative and explore new directions.

### Possible Outcomes

- Outcome "BENCHMARK_FAIL" means that the constraint was rejected because it did not sufficiently improve performance across runtime and objective value measurements.
- Outcome "PROOF_FAIL" means that the constraint did successfully pass benchmark but was rejected by the redundancy prover. Note that false negatives are possible if the constraint/proof was too convoluted. The same idea may still be used with a syntactically simpler/better implementation.
- Outcome "SUCCESS" means that the constraint was accepted because it passed the benchmark and the redundancy prover.

{attempt_blocks}
### State Notes

- `optimal`: status `OPTIMAL` (optimality or unsatisfiability proven).
- `sat`: status `FEASIBLE` (a feasible/satisfying solution, but not proven optimal).
- `timeout`: status `TIMEOUT` (timeout before any solution was found).
- `error`: status `ERROR`.
- Geomeans are computed over all instances that are optimal (for geomean optimality-time) or feasible+optimal (for geomean objective-value).
"""

ATTEMPT_TEMPLATE = """### Attempt {index}

- **Name:** {name}
- **Description:** {description}
- **Incumbent geomean optimality time:** {inc_geomean_opt_time}
- **New geomean optimality time:** {new_geomean_opt_time}
- **Incumbent geomean objective value:** {inc_geomean_objective}
- **New geomean objective value:** {new_geomean_objective}
- **Code:** `{code}`
- **Outcome:** {outcome}
- **Incumbent counts (optimal | feasible | timeout | error):** {incumbent_counts}
- **New counts (optimal | feasible | timeout | error):** {new_counts}
"""


def _format_state_counts(benchmark: minizinc_benchmark.BenchmarkResult) -> str:
    counts = {status: 0 for status in minizinc_benchmark.SolveStatus}
    for inst in benchmark.instances:
        for run in benchmark.runs_by_instance.get(inst, []):
            counts[run.status] += 1
    return (
        f"{counts[minizinc_benchmark.SolveStatus.OPTIMAL]} | "
        f"{counts[minizinc_benchmark.SolveStatus.FEASIBLE]} | "
        f"{counts[minizinc_benchmark.SolveStatus.TIMEOUT]} | "
        f"{counts[minizinc_benchmark.SolveStatus.ERROR]}"
    )


def _format_metric(value: float | None, *, suffix: str = "") -> str:
    return "n/a" if value is None else f"{value:.5g}{suffix}"


def get_user_prompt(
    mzn_content: str,
    previous_attempts: list[PreviousConstraintAttempt],
    num_constraints: int = 1,
) -> str:
    previous_section = ""
    if previous_attempts:
        attempt_blocks = []
        for i, attempt in enumerate(previous_attempts, 1):
            benchmark_pair = [attempt.incumbent_benchmark, attempt.new_benchmark]
            opt_geomean = minizinc_benchmark.compute_result_geomean_opt_time(benchmark_pair)
            obj_geomean = minizinc_benchmark.compute_geomean_objective(benchmark_pair)
            inc_opt_geo, new_opt_geo = (opt_geomean + [None, None])[:2]
            inc_obj_geo, new_obj_geo = (obj_geomean + [None, None])[:2]
            attempt_blocks.append(
                ATTEMPT_TEMPLATE.format(
                    index=i,
                    name=attempt.name,
                    description=attempt.description,
                    inc_geomean_opt_time=_format_metric(inc_opt_geo, suffix="s"),
                    new_geomean_opt_time=_format_metric(new_opt_geo, suffix="s"),
                    inc_geomean_objective=_format_metric(inc_obj_geo),
                    new_geomean_objective=_format_metric(new_obj_geo),
                    code=attempt.code,
                    outcome=attempt.outcome,
                    incumbent_counts=_format_state_counts(attempt.incumbent_benchmark),
                    new_counts=_format_state_counts(attempt.new_benchmark),
                )
            )
        previous_section = PREVIOUS_ATTEMPTS_SECTION_TEMPLATE.format(attempt_blocks="".join(attempt_blocks))

    return f"""# Task

Analyze the following MiniZinc model and suggest **{num_constraints}** redundant constraints that will greatly improve solver performance.

## MiniZinc Model

```minizinc
{mzn_content}
```
{previous_section}
## Required Output

Provide:

For each constraint:

1. A short name (max 30 chars)
2. A 1-2 sentence description (what it does + why it helps solver performance)
3. The constraint code as a single line, wrapped in `()` and annotated with `::redundant`

## Key Requirements

- **Non-trivial**: Don't just rearrange existing constraints
- **Novel**: Syntactically different from anything already in the model
- **Deep insight**: Combine information from multiple constraints
- **Think low-level**: Consider FlatZinc constraints, auxiliary variables, and propagation
- **Logically implied**: Must not change the solution space

Return JSON only in the specified schema. Do not include any other text.
**Be creative and find non-obvious implications!**"""


def _normalize_constraint_code(code: str) -> str:
    s = " ".join((code or "").strip().split())
    if not s.endswith(";"):
        s += ";"
    if "::redundant" not in s.replace(" ", ""):
        s = s.rstrip(";").rstrip() + " ::redundant;"
    if not s.lstrip().startswith("constraint"):
        s = "constraint " + s
    return s


def elicit_redundant_constraints(
    mzn_path: Path,
    model_name: str,
    reasoning_effort: str,
    num_constraints: int = 1,
    previous_attempts: list[PreviousConstraintAttempt] = None,
) -> ImproveBatchResult:
    if previous_attempts is None:
        previous_attempts = []

    num_constraints = max(int(num_constraints), 1)

    mzn_content = mzn_path.read_text(encoding="utf-8")

    log.info(
        "Requesting redundant constraints",
        mzn_path=str(mzn_path),
        model_name=model_name,
        reasoning_effort=reasoning_effort,
        num_constraints=num_constraints,
        previous_attempts=len(previous_attempts),
    )

    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": get_user_prompt(mzn_content, previous_attempts, num_constraints=num_constraints)}
    ]

    try:
        response, usage = helpers_llm_config.completion_with_retries(
            litellm,
            model=model_name,
            messages=messages,
            response_format=RedundantConstraintBatch,
            reasoning_effort=reasoning_effort,
            timeout_s=60 * 60,
            max_attempts=5,
            sleep_s=10.0,
        )
        content = response.choices[0].message.content or ""
        parsed = RedundantConstraintBatch.model_validate_json(content)
        constraints = list(parsed.constraints)
    except Exception as exc:  # noqa: BLE001
        log.exception("Constraint sampling failed", error=str(exc))
        return ImproveBatchResult(success=False, constraints=[], error_message=str(exc), llm_usage={})

    if len(constraints) != num_constraints:
        log.warning("LLM returned unexpected constraint count", expected=num_constraints, got=len(constraints))

    normalized: list[ImproveResult] = []
    for c in constraints:
        normalized.append(
            ImproveResult(
                success=True,
                constraint_name=(c.name or "").strip(),
                constraint_description=(c.description or "").strip(),
                constraint_code=_normalize_constraint_code(c.code),
                error_message="",
            )
        )

    log.info("Received constraints", constraints=len(normalized), llm_usage=usage.to_dict())
    return ImproveBatchResult(success=True, constraints=normalized, error_message="", llm_usage=usage.to_dict())
