"""
Structured logging with Rich-compatible console output.

Features:
- structlog for structured logging
- Rich progress bars that coexist with log output
- JSON file logging with full data
- Per-thread file logging for concurrent workloads
- Keys prefixed with '_' are hidden from console (for large payloads)
"""

import logging
import os
import sys
import threading
import time
from pathlib import Path
from contextlib import contextmanager
from typing import Generator

import structlog
from rich.console import Console
from rich.logging import RichHandler
from rich.progress import (
    Progress,
    SpinnerColumn,
    BarColumn,
    TextColumn,
    TimeElapsedColumn,
    TaskProgressColumn,
    MofNCompleteColumn,
)

# Shared console - MUST be used by both RichHandler and Progress
_console = Console(stderr=True)

# Global reference to active Progress (if any)
_active_progress: Progress | None = None

# Thread-local storage for per-thread log file path
_thread_log_file = threading.local()


class ProgressAwareHandler(RichHandler):
    """RichHandler that coordinates with active Progress displays."""

    def emit(self, record: logging.LogRecord) -> None:
        """Emit a log record, coordinating with any active Progress."""
        global _active_progress

        if _active_progress is not None and _active_progress.live.is_started:
            # Use Progress's print mechanism to avoid corruption
            try:
                msg = self.format(record)
                _active_progress.console.print(msg, highlight=False)
            except Exception:
                self.handleError(record)
        else:
            super().emit(record)


class ThreadFileHandler(logging.Handler):
    """Handler that writes to a per-thread file based on thread-local storage.

    Use with `thread_log_to_file()` context manager to set the file path.
    """

    def emit(self, record: logging.LogRecord) -> None:
        file_path = getattr(_thread_log_file, 'path', None)
        if file_path is None:
            return

        try:
            msg = self.format(record)
            file_path.parent.mkdir(parents=True, exist_ok=True)
            with open(file_path, 'a', encoding='utf-8') as f:
                f.write(msg + '\n')
        except Exception:
            self.handleError(record)


@contextmanager
def thread_log_to_file(file_path: Path | str | None) -> Generator[None, None, None]:
    """Context manager to direct this thread's logs to a specific file.

    Works with ThreadFileHandler. Logs go to both console and the specified file.

    Args:
        file_path: Path to log file, or None to disable thread file logging

    Example:
        with thread_log_to_file(Path("logs/run_1.log")):
            log.info("This goes to console AND logs/run_1.log")
    """
    old_path = getattr(_thread_log_file, 'path', None)
    _thread_log_file.path = Path(file_path) if file_path else None
    try:
        yield
    finally:
        if old_path is None:
            if hasattr(_thread_log_file, 'path'):
                delattr(_thread_log_file, 'path')
        else:
            _thread_log_file.path = old_path


def setup_logging(
    log_file: str | None = None,
    level: int = logging.INFO,
    enable_console: bool = True,
    enable_thread_file_logging: bool = False,
) -> structlog.stdlib.BoundLogger:
    """
    Configure structlog with optional JSON file logging and per-thread file logging.

    Args:
        log_file: Path to JSON log file (None to disable file logging)
        level: Logging level (default: INFO)
        enable_console: Enable console output (default: True)
        enable_thread_file_logging: Enable per-thread file logging via thread_log_to_file()

    Returns:
        Configured structlog logger
    """

    def add_process_info(_, __, event_dict):
        """Add process and thread identifiers."""
        event_dict["pid"] = os.getpid()
        event_dict["thread"] = threading.current_thread().name
        return event_dict

    def filter_private_keys(_, __, event_dict):
        """Remove keys starting with '_' (large payloads for file-only logging)."""
        return {k: v for k, v in event_dict.items() if not k.startswith("_")}

    def simple_renderer(_, __, event_dict):
        """Render event_dict as simple key=value string for RichHandler."""
        event = event_dict.pop("event", "")
        # Build key=value pairs
        pairs = " ".join(f"{k}={v}" for k, v in sorted(event_dict.items()))
        return f"{event}  {pairs}" if pairs else event

    # Shared processors
    shared_processors = [
        structlog.contextvars.merge_contextvars,
        structlog.processors.add_log_level,
        add_process_info,
        structlog.processors.TimeStamper(fmt="%H:%M:%S"),
    ]

    # Reset root logger
    root_logger = logging.getLogger()
    root_logger.handlers.clear()
    root_logger.setLevel(level)

    # Console Handler - use ProgressAwareHandler with shared console
    if enable_console:
        console_handler = ProgressAwareHandler(
            console=_console,
            rich_tracebacks=True,
            show_time=True,
            show_level=True,
            show_path=False,
            markup=False,
        )
        console_handler.setLevel(level)

        console_formatter = structlog.stdlib.ProcessorFormatter(
            foreign_pre_chain=shared_processors,
            processors=[
                structlog.stdlib.ProcessorFormatter.remove_processors_meta,
                filter_private_keys,
                simple_renderer,
            ],
        )
        console_handler.setFormatter(console_formatter)
        root_logger.addHandler(console_handler)

    # Global File Handler - JSON with all data including private keys
    if log_file:
        Path(log_file).parent.mkdir(parents=True, exist_ok=True)
        file_handler = logging.FileHandler(log_file, encoding="utf-8")
        file_handler.setLevel(level)

        file_formatter = structlog.stdlib.ProcessorFormatter(
            foreign_pre_chain=shared_processors,
            processors=[
                structlog.stdlib.ProcessorFormatter.remove_processors_meta,
                structlog.processors.JSONRenderer(),
            ],
        )
        file_handler.setFormatter(file_formatter)
        root_logger.addHandler(file_handler)

    # Per-thread File Handler - JSON with all data (use with thread_log_to_file())
    if enable_thread_file_logging:
        thread_handler = ThreadFileHandler()
        thread_handler.setLevel(logging.DEBUG)  # Capture all levels in thread files

        thread_formatter = structlog.stdlib.ProcessorFormatter(
            foreign_pre_chain=shared_processors,
            processors=[
                structlog.stdlib.ProcessorFormatter.remove_processors_meta,
                structlog.processors.JSONRenderer(),
            ],
        )
        thread_handler.setFormatter(thread_formatter)
        root_logger.addHandler(thread_handler)

    # Configure structlog
    structlog.configure(
        processors=[
            *shared_processors,
            structlog.stdlib.ProcessorFormatter.wrap_for_formatter,
        ],
        logger_factory=structlog.stdlib.LoggerFactory(),
        cache_logger_on_first_use=True,
    )

    return structlog.get_logger()


def get_logger(name: str | None = None) -> structlog.stdlib.BoundLogger:
    """Get a logger instance, optionally with a name bound to context."""
    log = structlog.get_logger()
    if name:
        log = log.bind(logger=name)
    return log


@contextmanager
def logging_progress(*columns, **kwargs) -> Generator[Progress, None, None]:
    """
    Context manager for Progress that coordinates with logging.

    Use this instead of Progress() directly to ensure logs display correctly.
    """
    global _active_progress

    if not columns:
        columns = (
            SpinnerColumn(),
            TextColumn("[bold]{task.description}"),
            BarColumn(bar_width=30),
            TaskProgressColumn(),
            MofNCompleteColumn(),
            TimeElapsedColumn(),
        )

    kwargs.setdefault("console", _console)
    kwargs.setdefault("refresh_per_second", 10)

    progress = Progress(*columns, **kwargs)

    try:
        _active_progress = progress
        with progress:
            yield progress
    finally:
        _active_progress = None


# --- Demo ---

def run_demo():
    """
    Demo: 2-level nested progress bars with structured logging.
    Total runtime: ~60 seconds
    """

    log = setup_logging(log_file="demo_output.jsonl")
    log.info("Starting batch processing demo", total_duration_sec=60)

    # Configuration: 5 batches × 12 items × 1s = 60s total
    num_batches = 5
    items_per_batch = 12
    sleep_per_item = 1.0

    with logging_progress() as progress:
        outer_task = progress.add_task("[cyan]Overall", total=num_batches)

        for batch_id in range(num_batches):
            log.info("Starting batch", batch_id=batch_id, items=items_per_batch)

            inner_task = progress.add_task(
                f"[yellow]  └─ Batch {batch_id}",
                total=items_per_batch,
            )

            for item_idx in range(items_per_batch):
                time.sleep(sleep_per_item)
                progress.update(inner_task, advance=1)

                # Log every 3rd item
                if item_idx % 3 == 0:
                    quality_score = 0.85 + (item_idx * 0.01)
                    log.info(
                        "Processed item",
                        batch_id=batch_id,
                        item=item_idx,
                        quality=f"{quality_score:.2f}",
                        _raw_result={
                            "vectors": list(range(50)),
                            "metadata": {"batch": batch_id, "idx": item_idx},
                        },
                    )

            progress.remove_task(inner_task)
            progress.update(outer_task, advance=1)
            log.info("Batch complete", batch_id=batch_id, items_processed=items_per_batch)

    log.info("Demo finished", total_batches=num_batches, total_items=num_batches * items_per_batch)
    _console.print("\n[bold green]✓[/] Check [bold]demo_output.jsonl[/] for full payloads")


if __name__ == "__main__":
    run_demo()
