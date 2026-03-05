from __future__ import annotations

import os
import random
import time
from dataclasses import asdict, dataclass
from typing import Any, Optional
from pathlib import Path

import structlog

log = structlog.get_logger()



def get_llm_config(key: str) -> dict:
    config = LLM_CONFIG[key]
    if isinstance(config, list):
        return random.choice(config)
    return config


def extract_cost_ct(response) -> float:
    """Extract cost in cents from a litellm response.

    Args:
        response: A litellm response object with _hidden_params containing response_cost.

    Returns:
        Cost in cents (float). Returns 0.0 if cost cannot be extracted.
    """
    if (hasattr(response, '_hidden_params')
        and 'response_cost' in response._hidden_params
        and response._hidden_params['response_cost'] is not None):
        return response._hidden_params['response_cost'] * 100.0
    else:
        log.warning('No response cost found for response.', _llm_response=response)
        return 0.0


@dataclass(frozen=True)
class LLMUsage:
    input_tokens: Optional[int] = None
    cached_tokens: Optional[int] = None
    output_tokens: Optional[int] = None
    total_tokens: Optional[int] = None
    cost_ct: float = 0.0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def extract_usage(response: Any) -> LLMUsage:
    cost_ct = extract_cost_ct(response)

    usage_obj = getattr(response, "usage", None)
    usage: dict[str, Any] = {}
    if usage_obj is None:
        usage = {}
    elif isinstance(usage_obj, dict):
        usage = usage_obj
    else:
        # pydantic / openai types
        if hasattr(usage_obj, "model_dump"):
            usage = usage_obj.model_dump()
        elif hasattr(usage_obj, "dict"):
            usage = usage_obj.dict()
        else:
            try:
                usage = dict(usage_obj)  # type: ignore[arg-type]
            except Exception:  # noqa: BLE001
                usage = {}

    input_tokens = usage.get("prompt_tokens", usage.get("input_tokens"))
    output_tokens = usage.get("completion_tokens", usage.get("output_tokens"))
    total_tokens = usage.get("total_tokens")

    cached_tokens: Optional[int] = None
    prompt_details = usage.get("prompt_tokens_details") or {}
    if isinstance(prompt_details, dict) and prompt_details.get("cached_tokens") is not None:
        cached_tokens = prompt_details.get("cached_tokens")

    if cached_tokens is None:
        hidden = getattr(response, "_hidden_params", None)
        if isinstance(hidden, dict):
            maybe = hidden.get("cached_tokens")
            if maybe is not None:
                cached_tokens = maybe

    def _to_int_or_none(x: Any) -> Optional[int]:
        if x is None:
            return None
        try:
            return int(x)
        except Exception:  # noqa: BLE001
            return None

    return LLMUsage(
        input_tokens=_to_int_or_none(input_tokens),
        cached_tokens=_to_int_or_none(cached_tokens),
        output_tokens=_to_int_or_none(output_tokens),
        total_tokens=_to_int_or_none(total_tokens),
        cost_ct=float(cost_ct),
    )


def completion_with_retries(
    litellm: Any,
    *,
    model: str,
    messages: list[dict[str, Any]],
    reasoning_effort: Optional[str] = None,
    max_tokens: Optional[int] = None,
    tools: Any = None,
    tool_choice: Any = None,
    response_format: Any = None,
    timeout_s: float = 1800,
    max_attempts: int = 5,
    sleep_s: float = 10.0,
    extra_kwargs: Optional[dict[str, Any]] = None,
) -> tuple[Any, LLMUsage]:
    extra_kwargs = dict(extra_kwargs or {})

    if model.startswith("openrouter/"):
        my_fallbacks = ['atlas-cloud/fp8', 'siliconflow/fp8']
        extra_kwargs.setdefault(
            "extra_body",
            {
                "provider": {
                    # parasil/fp8 -- tests with deepseek v3.2 sometimes included the full lean file
                    # phala -- sometimes disconnects
                    # NEVER USE because of truncation issues: "deepinfra/fp8", "deepinfra/fp4"
                    "order": ["novita/fp8", "novita/fp4"] + my_fallbacks,
                    "allow_fallbacks": True,
                }
            },
        )

    last_exc: Optional[Exception] = None
    for attempt in range(max_attempts):
        try:
            kwargs: dict[str, Any] = {
                "model": model,
                "messages": messages,
                "max_retries": 1,
                "timeout": timeout_s,
                **extra_kwargs,
            }
            if tools is not None:
                kwargs["tools"] = tools
            if tool_choice is not None:
                kwargs["tool_choice"] = tool_choice
            if response_format is not None:
                kwargs["response_format"] = response_format
            if reasoning_effort is not None:
                kwargs["reasoning_effort"] = reasoning_effort
            if max_tokens is not None:
                kwargs["max_tokens"] = max_tokens
            if 'anthropic/' not in model and 'reasoning_effort' in kwargs:
                kwargs["allowed_openai_params"] = ['reasoning_effort']

            response = litellm.completion(**kwargs)
            return response, extract_usage(response)
        except Exception as exc:  # noqa: BLE001
            last_exc = exc
            log.warning(
                "LLM call failed",
                llm_model=model,
                attempt=attempt,
                max_attempts=max_attempts,
                error=str(exc),
            )
            if attempt < max_attempts - 1:
                time.sleep(sleep_s)

    assert last_exc is not None
    raise last_exc
