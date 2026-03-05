from dataclasses import dataclass, field
import re
from pathlib import Path

import litellm
import structlog

from . import helpers_llm_config
from . import verifier_lean

log = structlog.get_logger()

PROMPT_SYSTEM_MANUAL_COT = (Path(__file__).parent / "prompts" / "prompt_system_manual_cot.txt").read_text()
PROMPT_SYSTEM = (Path(__file__).parent / "prompts" / "prompt_system.txt").read_text()


@dataclass
class ProveLeanCodeResult:
    success: bool
    total_cost_ct: float
    turns_needed: int = -1 # if success, number of steps needed to prove
    llm_usage: dict = field(default_factory=dict)
    trace: list[dict] = field(default_factory=list)
    proven_lean_code: str = ""




"""
Extract the Lean 4 proof code from the text.

Args:
    text: The text to extract the Lean 4 proof code from.

Returns:
    A tuple containing a boolean indicating whether the extraction was successful, and a string containing the Lean 4 proof code or the error message.
"""
def extract_lean_proof_content(text: str) -> tuple[bool, str]:
    if not (text or "").strip():
        return False, "Extracting Lean code failed: response was empty."

    def _extract_from_lean_block(lean_block: str) -> tuple[bool, str]:
        if "```" in lean_block:
            return False, "Extracting Lean code failed: response must contain exactly one code block."
        theorem_match = re.search(r"theorem\s+.*?\s*:=\s*by\b(.*)$", lean_block, re.DOTALL)
        if not theorem_match:
            # Also accept a block that contains only the proof term, starting at `by ...`.
            by_match = re.search(r"^\s*by\b(.*)$", lean_block, re.DOTALL)
            if by_match:
                return True, by_match.group(1)
            # As a last resort, accept any non-empty Lean block as "proof body" (everything after `by`).
            if lean_block.strip():
                return True, "\n" + lean_block.strip("\n")
            return False, "Extracting Lean code failed. No matching 'theorem ... := by' or leading 'by', and the lean code block was empty."
        return True, theorem_match.group(1)

    # Preferred: response is only a single code block (no extra text).
    block_match = re.match(
        r"^\s*```(?:lean4?|lean)?\s*\n(.*)\n?\s*```\s*$",
        text,
        re.DOTALL | re.IGNORECASE,
    )
    if block_match:
        return _extract_from_lean_block(block_match.group(1))

    # Fallback: extract the last Lean-ish code block even if extra text is present.
    matches = re.findall(r"```(?:lean4?|lean)?\s*\n(.*?)\n\s*```", text, re.DOTALL | re.IGNORECASE)
    if matches:
        return _extract_from_lean_block(matches[-1])

    # Last resort: some models omit code fences entirely.
    return _extract_from_lean_block(text)



def get_initial_messages(lean_code: str, reasoning_setting: str) -> list[dict]:
    system_prompt = PROMPT_SYSTEM if reasoning_setting is not None else PROMPT_SYSTEM_MANUAL_COT
    user_prompt = (
        "Prove this Lean theorem:\n\n"
        f"```lean\n{lean_code.strip()}\n```\n\n"
        "Return only a single ```lean``` (or ```lean4```) code block containing the full theorem with its proof. No other text.\n"
        "Only use lemmas/tactics you are confident exist and whose type/signature matches the goal; do not guess names.\n"
        "When in doubt, prefer a longer proof using simpler steps.\n"
    )


    messages = []
    messages.append({"role": "system", "content": system_prompt})
    messages.append({"role": "user", "content": user_prompt})

    return messages


def _sum_optional_int(a: int | None, b: int | None) -> int | None:
    if a is None and b is None:
        return None
    return int(a or 0) + int(b or 0)


def _accumulate_usage(total: helpers_llm_config.LLMUsage, add: helpers_llm_config.LLMUsage) -> helpers_llm_config.LLMUsage:
    return helpers_llm_config.LLMUsage(
        input_tokens=_sum_optional_int(total.input_tokens, add.input_tokens),
        cached_tokens=_sum_optional_int(total.cached_tokens, add.cached_tokens),
        output_tokens=_sum_optional_int(total.output_tokens, add.output_tokens),
        total_tokens=_sum_optional_int(total.total_tokens, add.total_tokens),
        cost_ct=float(total.cost_ct) + float(add.cost_ct),
    )


def _llm_call(model_name, messages, reasoning_setting) -> tuple[any, helpers_llm_config.LLMUsage]:
    log.debug('Starting LLM call.', llm_messages=messages, llm_reasoning_setting=reasoning_setting)
    response, usage = helpers_llm_config.completion_with_retries(
        litellm,
        model=model_name,
        messages=messages,
        reasoning_effort=reasoning_setting,
        max_tokens=16384,
        timeout_s=3600,
        max_attempts=3,
        sleep_s=10.0,
    )
    log.debug('Received response from model.', _llm_response=response)
    messages.append(response.choices[0].message)
    return response, usage



def prove_lean_code(
        lean_problem: str,
        model_name: str,
        max_turns: int = 5,
        reasoning_setting: str = 'high',
        capture_trace: bool = False,
    ) -> ProveLeanCodeResult:
    if "deepseek-prover-v2-671b" in model_name:
        return prove_lean_code_deepseek_prover(
            lean_problem=lean_problem,
            model_name=model_name,
            max_turns=max_turns,
            reasoning_setting=reasoning_setting,
            capture_trace=capture_trace,
        )

    with structlog.contextvars.bound_contextvars(model_name=model_name, max_passes=max_turns, reasoning_setting=reasoning_setting):
        log.info(f'Starting proof attempt.', _lean_problem=lean_problem)

        messages = get_initial_messages(lean_problem, reasoning_setting)
        lean_problem_prefix = re.sub(r'\bsorry\s*$', '', lean_problem)

        total_cost_ct = 0.0
        total_usage = helpers_llm_config.LLMUsage()
        trace: list[dict] = []


        for turn in range(max_turns):
            with structlog.contextvars.bound_contextvars(turn=turn):
                log.info(f'Starting turn {turn}.')

                try:
                    response, usage = _llm_call(model_name, messages, reasoning_setting)
                except Exception as exc:  # noqa: BLE001
                    log.exception("LLM call failed in proof attempt", error=str(exc))
                    if capture_trace:
                        trace.append({"turn": turn, "error": str(exc), "stage": "llm_call"})
                    return ProveLeanCodeResult(
                        success=False,
                        turns_needed=-1,
                        total_cost_ct=total_cost_ct,
                        llm_usage=total_usage.to_dict(),
                        trace=trace,
                        proven_lean_code="",
                    )

                total_cost_ct += usage.cost_ct
                total_usage = _accumulate_usage(total_usage, usage)
                response_content = response.choices[0].message.content or ''

                log.info(f'Received response from model (cost: {usage.cost_ct}ct, total {total_cost_ct}ct). Checking for validity.', llm_usage=usage.to_dict(), llm_cost_ct=usage.cost_ct, total_cost_ct=total_cost_ct, _llm_response=response, _llm_response_content=response_content)

                valid, proof_code_or_error = extract_lean_proof_content(response_content)
                verify_result = None
                if not valid:
                    feedback = proof_code_or_error
                else:
                    lean_code = lean_problem_prefix + proof_code_or_error
                    verify_result = verifier_lean.verify_lean_proof(lean_code)
                    if verify_result.success:
                        log.info(f'Turn {turn} successful.', extract_lean_success=valid, verify_lean_success=verify_result.success, _lean_code_proof=proof_code_or_error, _lean_code_full=lean_code, total_cost_ct=total_cost_ct)
                        return ProveLeanCodeResult(
                            success=True,
                            turns_needed=turn + 1,
                            total_cost_ct=total_cost_ct,
                            llm_usage=total_usage.to_dict(),
                            trace=trace,
                            proven_lean_code=lean_code,
                        )
                    else:
                        feedback = (
                            f"## Lean return code: \n {verify_result.return_code} \n\n"
                            f"## Lean stdout: \n {verify_result.lean_stdout} \n\n"
                            f"## Lean stderr: \n {verify_result.lean_stderr} \n\n"
                            f"## Lean proof line info: \n {verify_result.line_info}"
                        )

                if capture_trace:
                    trace.append(
                        {
                            "turn": turn,
                            "llm_usage": usage.to_dict(),
                            "extract_success": bool(valid),
                            "verify_success": bool(getattr(verify_result, "success", False)),
                            "lean_return_code": None if verify_result is None else getattr(verify_result, "return_code", None),
                            "lean_stdout": None if verify_result is None else (verify_result.lean_stdout or ""),
                            "lean_stderr": None if verify_result is None else (verify_result.lean_stderr or ""),
                            "line_info": None if verify_result is None else getattr(verify_result, "line_info", None),
                            "llm_response_content": (response_content or ""),
                            "feedback": (feedback or ""),
                        }
                    )

                log.info(
                    f"Turn {turn} not successful.",
                    extract_lean_success=bool(valid),
                    verify_lean_success=False,
                    _llm_feedback=feedback,
                    _proof_code_or_extract_error=proof_code_or_error,
                    _verify_result=verify_result,
                )
                refine_prompt = (
                    "The previous Lean proof (the last code block you produced) did not compile. "
                    "Use the feedback below to diagnose and fix the proof.\n\n"
                    f"<FEEDBACK>\n{feedback}\n</FEEDBACK>\n\n"
                    "In your response (STRICT):\n"
                    "- Output only a single ```lean``` (or ```lean4```) code block.\n"
                    "- Inside the code block, start with a medium-detail `/- Diagnosis: ... -/` comment (5-20 lines) summarizing what exactly went wrong and what you will change.\n"
                    "- Then output the full theorem with a corrected proof (starting with `theorem`).\n\n"
                    "Rules:\n"
                    "- Treat the feedback as ground truth; fix the earliest error first.\n"
                    "- If Lean reports an `unknown constant`/`unknown identifier` for lemma/definition names, do not use that name again.\n"
                    "- Do not guess lemma names; ensure every lemma/tactic application typechecks. Prefer simpler steps when unsure."
                )
                messages.append({"role": "user", "content": refine_prompt})

        log.info('Verification failed.', total_cost_ct=total_cost_ct)
        return ProveLeanCodeResult(
            success=False,
            turns_needed=-1,
            total_cost_ct=total_cost_ct,
            llm_usage=total_usage.to_dict(),
            trace=trace,
            proven_lean_code="",
        )


def prove_lean_code_deepseek_prover(
        lean_problem: str,
        model_name: str,
        max_turns: int = 5,
        reasoning_setting: str = 'high',
        capture_trace: bool = False,
        all_turns_use_initial_prompt: bool = True,
    ) -> ProveLeanCodeResult:
    use_cot_prompt = reasoning_setting is not None
    reasoning_mode = 'true' if use_cot_prompt else 'false'

    def _build_deepseek_prover_prompt(local_lean_problem: str, local_use_cot_prompt: bool) -> str:
        prompt = (
            "Complete the following Lean 4 code:\n"
            "```lean4\n"
            f"{local_lean_problem.strip()}\n"
            "```\n"
        )
        if local_use_cot_prompt:
            prompt += (
                "Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.\n"
                "The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.\n"
            )
        return prompt

    def _get_deepseek_prover_messages(local_lean_problem: str, local_use_cot_prompt: bool) -> list[dict[str, str]]:
        return [{"role": "user", "content": _build_deepseek_prover_prompt(local_lean_problem, local_use_cot_prompt)}]

    def _extract_chat_completion_content(response: any) -> str:
        choices = getattr(response, 'choices', None)
        if choices:
            first_choice = choices[0]
            message = getattr(first_choice, 'message', None)
            if message is not None:
                content = getattr(message, 'content', None)
                if content is not None:
                    return str(content)
            if isinstance(first_choice, dict):
                first_message = first_choice.get('message') or {}
                content = first_message.get('content')
                if content is not None:
                    return str(content)

        if isinstance(response, dict):
            response_choices = response.get('choices') or []
            if response_choices:
                first_message = response_choices[0].get('message') or {}
                return str(first_message.get('content') or '')
        return ''

    def _append_deepseek_manual_patch(
        current_messages: list[dict[str, str]],
        model_output: str,
        feedback: str,
        base_prompt: str,
    ) -> list[dict[str, str]]:
        return [
            *current_messages,
            {"role": "assistant", "content": (model_output or "").strip()},
            {
                "role": "user",
                "content": (
                    "Wait, this is wrong. The lean compiler reports the following error:\n"
                    f"{feedback}\n\n"
                    f"{base_prompt}"
                ),
            },
        ]

    with structlog.contextvars.bound_contextvars(model_name=model_name, max_passes=max_turns, reasoning_setting=reasoning_mode):
        log.info('Starting DeepSeek-Prover proof attempt.', _lean_problem=lean_problem)

        base_messages = _get_deepseek_prover_messages(lean_problem, use_cot_prompt)
        messages = list(base_messages)
        lean_problem_prefix = re.sub(r'\bsorry\s*$', '', lean_problem)

        total_cost_ct = 0.0
        total_usage = helpers_llm_config.LLMUsage()
        trace: list[dict] = []

        for turn in range(max_turns):
            with structlog.contextvars.bound_contextvars(turn=turn):
                log.info(f'Starting turn {turn}.')

                try:
                    response = litellm.completion(
                        model=model_name,
                        messages=messages,
                        max_tokens=65000,
                        timeout=3600,
                        max_retries=100,

                        ## old decoding settings (deepseek-prover-v2-orig_prompt_cot)
                        #temperature=1.0,
                        #top_p=1.0,
                        #top_k=50,
                        ## new decoding settings (deepseek-prover-v2-orig_prompt_cot-pass_at_5, deepseek-prover-v2-orig_prompt_cot-pass_at_16)
                        temperature=1.0,
                        top_p=0.95,
                        #top_k=0,
                    )
                    usage = helpers_llm_config.extract_usage(response)
                except Exception as exc:  # noqa: BLE001
                    log.exception('DeepSeek-Prover call failed in proof attempt', error=str(exc))
                    if capture_trace:
                        trace.append({"turn": turn, "error": str(exc), "stage": "llm_call"})
                    return ProveLeanCodeResult(
                        success=False,
                        turns_needed=-1,
                        total_cost_ct=total_cost_ct,
                        llm_usage=total_usage.to_dict(),
                        trace=trace,
                        proven_lean_code="",
                    )

                total_cost_ct += usage.cost_ct
                total_usage = _accumulate_usage(total_usage, usage)
                response_content = _extract_chat_completion_content(response)

                log.info(
                    f'Received response from DeepSeek-Prover (cost: {usage.cost_ct}ct, total {total_cost_ct}ct). Checking for validity.',
                    llm_usage=usage.to_dict(),
                    llm_cost_ct=usage.cost_ct,
                    total_cost_ct=total_cost_ct,
                    _llm_response=response,
                    _llm_response_content=response_content,
                )

                valid, proof_code_or_error = extract_lean_proof_content(response_content)
                verify_result = None
                if not valid:
                    feedback = proof_code_or_error
                else:
                    lean_code = lean_problem_prefix + proof_code_or_error
                    verify_result = verifier_lean.verify_lean_proof(lean_code)
                    if verify_result.success:
                        log.info(
                            f'Turn {turn} successful.',
                            extract_lean_success=valid,
                            verify_lean_success=verify_result.success,
                            _lean_code_proof=proof_code_or_error,
                            _lean_code_full=lean_code,
                            total_cost_ct=total_cost_ct,
                        )
                        return ProveLeanCodeResult(
                            success=True,
                            turns_needed=turn + 1,
                            total_cost_ct=total_cost_ct,
                            llm_usage=total_usage.to_dict(),
                            trace=trace,
                            proven_lean_code=lean_code,
                        )
                    feedback = (
                        f"## Lean return code: \n {verify_result.return_code} \n\n"
                        f"## Lean stdout: \n {verify_result.lean_stdout} \n\n"
                        f"## Lean stderr: \n {verify_result.lean_stderr} \n\n"
                        f"## Lean proof line info: \n {verify_result.line_info}"
                    )

                if capture_trace:
                    trace.append(
                        {
                            "turn": turn,
                            "llm_usage": usage.to_dict(),
                            "extract_success": bool(valid),
                            "verify_success": bool(getattr(verify_result, "success", False)),
                            "lean_return_code": None if verify_result is None else getattr(verify_result, "return_code", None),
                            "lean_stdout": None if verify_result is None else (verify_result.lean_stdout or ""),
                            "lean_stderr": None if verify_result is None else (verify_result.lean_stderr or ""),
                            "line_info": None if verify_result is None else getattr(verify_result, "line_info", None),
                            "llm_response_content": (response_content or ""),
                            "feedback": (feedback or ""),
                        }
                    )

                log.info(
                    f'Turn {turn} not successful.',
                    extract_lean_success=bool(valid),
                    verify_lean_success=False,
                    _llm_feedback=feedback,
                    _proof_code_or_extract_error=proof_code_or_error,
                    _verify_result=verify_result,
                )

                if not all_turns_use_initial_prompt:
                    messages = _append_deepseek_manual_patch(
                        current_messages=messages,
                        model_output=response_content,
                        feedback=feedback,
                        base_prompt=base_messages[0]["content"],
                    )

        log.info('DeepSeek-Prover verification failed.', total_cost_ct=total_cost_ct)
        return ProveLeanCodeResult(
            success=False,
            turns_needed=-1,
            total_cost_ct=total_cost_ct,
            llm_usage=total_usage.to_dict(),
            trace=trace,
            proven_lean_code="",
        )
