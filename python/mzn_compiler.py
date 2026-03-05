import errno
import fcntl
from contextlib import contextmanager
import subprocess
import logging
import os
import time

from dataclasses import dataclass
from pathlib import Path

from . import verifier_lean

log = logging.getLogger(__name__)


@dataclass
class MznToLeanResult:
    success: bool
    lean_code: str
    compiler_stdout: str
    compiler_stderr: str

USE_RELEASE = True
build_type = 'Release' if USE_RELEASE else 'Debug'
build_dir = 'release' if USE_RELEASE else 'debug'
CMAKE_LOCK_PATH = Path("./.mzn2lean_cmake.lock")
CMAKE_LOCK_TIMEOUT_SECONDS = 60 * 5
CMAKE_LOCK_POLL_SECONDS = 1.0


@contextmanager
def _filesystem_cmake_lock():
    lock_fd = os.open(CMAKE_LOCK_PATH, os.O_CREAT | os.O_RDWR, 0o666)
    acquired = False
    lock_start = time.monotonic()
    try:
        while True:
            try:
                fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                acquired = True
                break
            except OSError as err:
                if err.errno not in (errno.EACCES, errno.EAGAIN):
                    raise
                waited = time.monotonic() - lock_start
                if waited >= CMAKE_LOCK_TIMEOUT_SECONDS:
                    raise TimeoutError(
                        f"Timed out after {CMAKE_LOCK_TIMEOUT_SECONDS}s waiting for CMake lock at {CMAKE_LOCK_PATH}"
                    ) from err
                time.sleep(CMAKE_LOCK_POLL_SECONDS)

        os.ftruncate(lock_fd, 0)
        lock_owner = f"pid={os.getpid()} host={os.uname().nodename} acquired_at={int(time.time())}\n"
        os.write(lock_fd, lock_owner.encode())
        os.fsync(lock_fd)
        yield
    finally:
        if acquired:
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
        os.close(lock_fd)

def ensure_compiled():
    with _filesystem_cmake_lock():

        subprocess.run(
            f'cmake -S . -B build/{build_dir} -DCMAKE_BUILD_TYPE={build_type} && cmake --build build/{build_dir} --target mzn2lean',
            cwd="./mzn-to-lean",
            shell=True,
            check=True,
            #capture_output=True,
        )

def mzn_to_lean(
    mzn_path: Path,
    validate_lean: bool = True,
    prove_non_redundant: bool = False,
    redundant_ann: str | None = None,
    cons_ann_ignore: str | None = None,
) -> MznToLeanResult:
    sep = "=" * 80

    log.info('Building mzn2lean...')

    log.info(f'{mzn_path}: compiling to Lean')
    log.debug(f'{sep}\n% MINIZINC FILE: {mzn_path}\n{mzn_path.read_text().strip()}\n{sep}\n')

    # execute ./mzn2lean problem_path
    cmd = [f"./mzn-to-lean/build/{build_dir}/mzn2lean", str(mzn_path)]
    if prove_non_redundant:
        cmd.append("--prove-non-redundant")
    if redundant_ann is not None:
        cmd.extend(["--redundant-ann", redundant_ann])
    if cons_ann_ignore is not None:
        cmd.extend(["--cons-ann-ignore", cons_ann_ignore])
    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True
    )
    lean_code = result.stdout#.split("========================================\n")

    if result.returncode != 0:
        log.error(f"{mzn_path}: Failed to compile to Lean: {result.stderr}")
        return MznToLeanResult(success=False, lean_code="", compiler_stdout=result.stdout, compiler_stderr=result.stderr)

    log.debug(f'{sep}\n-- LEAN CONTENT: {lean_code.strip()}\n{sep}\n')
    log.info(f'{mzn_path}: finished compiling to Lean')


    if validate_lean:
        log.info(f'{mzn_path}: validating Lean code')
        verify_result = verifier_lean.verify_lean_proof(lean_code, fill_line_info=False)
        # if "sorry" is in proof, lean only throws a warning and returns code 0 anyway
        if verify_result.return_code != 0:
            log.error(f"Failed to validate Lean code: {verify_result.return_code} {verify_result.lean_stdout + verify_result.lean_stderr}")
            return MznToLeanResult(success=False, lean_code=lean_code, compiler_stdout=result.stdout + result.stderr, compiler_stderr="!!!!! Generated lean program erroneous")
    return MznToLeanResult(success=True, lean_code=lean_code, compiler_stdout=result.stdout, compiler_stderr=result.stderr)
