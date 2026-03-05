import logging
import tempfile
import subprocess
import re
from dataclasses import dataclass
from pathlib import Path
from contextlib import ExitStack

log = logging.getLogger(__name__)


def _collect_line_info(proof_content: str, lean_program_path: Path, lean_output: str) -> str:
    lean_lines = proof_content.splitlines()
    pattern = re.compile(rf"{re.escape(str(lean_program_path))}:(\d+)(?::\d+)?")
    seen_lines: set[int] = set()
    line_info_entries: list[str] = []

    def _collect(text: str) -> None:
        for m in pattern.finditer(text or ''):
            try:
                ln = int(m.group(1))
            except Exception:
                continue
            if ln in seen_lines:
                continue
            seen_lines.add(ln)
            if 1 <= ln <= len(lean_lines):
                line_txt = lean_lines[ln - 1].rstrip()
            else:
                line_txt = "<line out of range>"
            line_info_entries.append(
                f"Line {lean_program_path.name}:{ln} is \"{line_txt}\""
            )

    _collect(lean_output)
    line_info = "\n".join(line_info_entries)
    return line_info

@dataclass
class ReplaceTheoremResult:
    success: bool
    theorem: str
    error_message: str

def replace_theorem(lean_template: str, lean_theorem: str) -> ReplaceTheoremResult:
    proof_match = re.search(r'theorem\s+.*?\s*:=\s*by\b(.*)$', lean_theorem, re.DOTALL)
    if proof_match:
        proof = proof_match.group(1)
    else:
        log.info(f"Could not extract theorem body. Regex searching for 'theorem ... by' found no match.")
        return ReplaceTheoremResult(success=False, theorem="", error_message="Could not extract theorem body. Regex searching for 'theorem ... by' found no match.")
    template_without_sorry = re.sub(r'\bsorry\s*$', '', lean_template)
    return ReplaceTheoremResult(success=True, theorem=template_without_sorry + proof, error_message="")


@dataclass
class VerifyResult:
    success: bool
    lean_stdout: str
    lean_stderr: str
    return_code: int = -1
    line_info: str = ""


def verify_lean_proof(proof_path_or_content: Path | str, timeout_s: int = 60 * 3, fill_line_info: bool = True) -> VerifyResult:
    with ExitStack() as stack:
        if isinstance(proof_path_or_content, Path):
            proof_path = proof_path_or_content
            proof_content = proof_path.read_text()
        else:
            tmpfile = stack.enter_context(tempfile.NamedTemporaryFile(delete=False))
            tmpfile.write(proof_path_or_content.encode('utf-8'))
            tmpfile.flush()
            proof_path = Path(tmpfile.name)
            proof_content = proof_path_or_content

        log.debug(f"{proof_path}: Verifying Lean proof")

        try:
            result = subprocess.run(
                ["lake", "env", "lean", "-Dlinter.all=false", str(proof_path)],
                cwd="./lean",
                capture_output=True,
                text=True,
                timeout=timeout_s,
            )
        except subprocess.TimeoutExpired:
            log.warning(f"{proof_path}: Lean code timed out after {timeout_s} seconds.")
            return VerifyResult(success=False, lean_stdout="", lean_stderr=f"Timeout: Lean code timed out after {timeout_s} seconds.")

        if fill_line_info:
            line_info = _collect_line_info(proof_content, proof_path, result.stdout + '\n' + result.stderr)
        else:
            line_info = ""
        was_success = result.returncode == 0 and 'sorry' not in (result.stdout + result.stderr).lower()

        return VerifyResult(
            success=was_success,
            return_code=result.returncode,
            lean_stdout=result.stdout,
            lean_stderr=result.stderr,
            line_info=line_info,
        )

