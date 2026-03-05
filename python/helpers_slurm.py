from __future__ import annotations

import math
import os
from datetime import datetime
from pathlib import Path
import random
import string
from typing import Any

import structlog

log = structlog.get_logger()


def create_slurm_tmp_folder(*, dt: datetime | None = None) -> Path:
    """Create a shared-folder location for Submitit/Slurm artifacts.

    We intentionally avoid /tmp here because compute nodes may not share it.
    """
    ts = (dt or datetime.now()).strftime("%Y-%m-%d_%H-%M-%S")
    suffix = ''.join(random.choices(string.ascii_letters + string.digits, k=6))

    base = os.environ.get("SLURM_TEMP_DIR", None)
    if base is not None:
        base = Path(base)
    else:
        base = Path("~/slurm_tmp").expanduser().resolve()
    base.mkdir(parents=True, exist_ok=True)

    pid = os.getpid()
    name = f"slurm_{ts}_{pid}_{suffix}"
    path = base / name
    path.mkdir(parents=True, exist_ok=False)
    return path


def configure_executor(
    executor: Any,
    *,
    timeout_s: float,
    timeout_padding_s: float = 60.0 * 30,
) -> None:
    """Slurm configuration for AutoMZN benchmarks.

    Reads SLURM_PARTITION and SLURM_CPU_FREQ from environment variables,
    falling back to sensible defaults.
    """
    partition = os.environ.get("SLURM_PARTITION", "sunnycove")
    cpu_freq = os.environ.get("SLURM_CPU_FREQ", "2400000")

    timeout_s = float(timeout_s)
    timeout_min = max(1, int(math.ceil((timeout_s + timeout_padding_s) / 60.0)))

    executor.update_parameters(
        cpus_per_task=1,
        mem_gb=16,
        timeout_min=timeout_min,
        slurm_partition=partition,
        slurm_additional_parameters={
            "cpu_freq": f"{cpu_freq}-{cpu_freq}:performance",
            "export": "ALL",
        },
    )

    log.info(
        "Configured Slurm executor for MiniZinc benchmarking",
        cpus_per_task=1,
        mem_gb=16,
        timeout_min=timeout_min,
        partition=partition,
        cpu_freq=cpu_freq,
    )
