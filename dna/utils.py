# License: Apache 2.0
# Code Adapted from: https://github.com/loganrjmurphy/LeanEuclid/blob/master/AutoFormalization/utils.py


# Standard Library Modules
import base64
import os
import shutil
import re
import signal
from collections import OrderedDict
from typing import Iterable
from typing import Optional, Pattern


def encode_image(image_path: str) -> str:
    with open(image_path, "rb") as image_file:
        encoded_string = base64.b64encode(image_file.read()).decode("utf-8")
    return encoded_string


def lean_error(error: str) -> str:
    return (
        "Your formalized statement is not a well-formed lean expression.\n\n"
        f"Here is the Lean error message: {error}\n\n"
        "Please try again and fix the error in your final formalized statement."
    )


def parse_error() -> str:
    return (
        "Your output is not in the desired format. "
        "Please output the formalized statement within triple angle brackets (<<< Lean expression here >>>)."
    )


def format_content(dataset: str, namespace: str, theorem_name: str, theorem: str, proof: str) -> str:
    # This function is deprecated and only kept for backward compatibility
    # ProofNet and DSL datasets don't use this function
    return ""


def remove_error_source(message: str) -> str:
    """
    Strip the leading error source from a Lean error message.

    Example:
    >>> remove_error_source(
        "/home/johndoe/.../result/proof/sample/2.lean:6:35: error: ..."
    )
    error: ...
    """
    return re.sub(r"/[^:]+:\d+:\d+: ", "", message)


def kill_process_group(pgid: int) -> None:
    """
    Kill all processes in the process group using ``SIGKILL``.
    Useful for killing z3 and cvc5 solvers spawned by a checker.

    :param pgid: ID of the process group to kill
    """
    try:
        os.killpg(pgid, signal.SIGKILL)
    except ProcessLookupError:
        # Process group already exited
        pass
    except PermissionError:
        print("⚠️  Insufficient permission to kill process group", pgid)


def merge_lean_sections(*snippets: Iterable[str]) -> str:
    """Merge multiple Lean code snippets.

    - All ``import`` statements are moved to the top, keeping first occurrence order.
    - Duplicate non-empty lines (after stripping) are removed while preserving
      the first appearance and original indentation.
    - Ensures at most one blank line separates logical sections.
    """

    import_lines = OrderedDict()
    open_lines = OrderedDict()
    open_scoped_lines = OrderedDict()
    set_option_lines = OrderedDict()
    body_lines: list[str] = []
    # Track seen non-empty body lines (by stripped content) to avoid
    # duplicate declarations across snippets while preserving first formatting.
    seen_body_lines = OrderedDict()
    # Ensure we don't introduce multiple top-level `noncomputable section`s
    seen_noncomputable_section = False

    def _append_blank_line() -> None:
        if body_lines and body_lines[-1] != "":
            body_lines.append("")

    for snippet in snippets:
        if not snippet:
            continue
        # Allow callers to pass raw strings or iterables of strings
        section = "\n".join(snippet) if isinstance(snippet, (list, tuple, set)) else str(snippet)
        lines = section.splitlines()
        if not lines:
            continue

        # Separate sections with one blank line (handled after imports collection)
        if body_lines:
            _append_blank_line()

        for raw_line in lines:
            line = raw_line.rstrip()
            stripped = line.strip()
            if not stripped:
                continue
            if stripped.startswith("import "):
                import_lines.setdefault(stripped, stripped)
                continue

            if stripped.startswith("open scoped "):
                open_scoped_lines.setdefault(stripped, line)
                continue

            if stripped.startswith("open "):
                open_lines.setdefault(stripped, line)
                continue

            if stripped.startswith("set_option "):
                set_option_lines.setdefault(stripped, line)
                continue

            # Handle special directives conservatively
            if stripped == "noncomputable section":
                if not seen_noncomputable_section:
                    seen_noncomputable_section = True
                    body_lines.append(line)
                # Skip subsequent duplicates to avoid nested sections by accident
                continue

            # Do NOT deduplicate bare `end` lines; they close sections/namespaces
            # and removing one could unbalance blocks.
            if stripped == "end":
                body_lines.append(line)
                continue

            # Deduplicate identical non-header lines by stripped content across snippets
            if stripped not in seen_body_lines:
                seen_body_lines[stripped] = line  # cache original formatting
                body_lines.append(line)

    merged_parts = []
    if import_lines:
        merged_parts.append("\n".join(import_lines.values()))

    if open_lines:
        merged_parts.append("\n".join(open_lines.values()))

    if open_scoped_lines:
        merged_parts.append("\n".join(open_scoped_lines.values()))

    if set_option_lines:
        merged_parts.append("\n".join(set_option_lines.values()))

    body = "\n".join(body_lines).strip()
    if body:
        merged_parts.append(body)

    merged = "\n\n".join(part for part in merged_parts if part)
    return (merged + "\n") if merged else ""


# ---- Generic helpers shared by checkers ----

def read_text_if_exists(path: Optional[str]) -> str:
    if not path:
        return ""
    try:
        with open(path, "r", encoding="utf-8") as handle:
            return handle.read()
    except OSError:
        return ""


def sanitize_identifier(name: str) -> str:
    try:
        return re.sub(r"[^A-Za-z0-9_]+", "_", str(name)).strip("_")
    except Exception:
        return "item"


def ensure_lean_tools_on_path(working_root: Optional[str] = None) -> None:
    """Ensure 'lake' and 'lean' are discoverable by adding common locations to PATH.

    Looks into ~/.elan/bin and optionally <working_root>/lean-env/bin.
    """
    def _add_dir(p: str):
        if p and os.path.isdir(p):
            cur = os.environ.get('PATH', '')
            paths = cur.split(os.pathsep) if cur else []
            if p not in paths:
                os.environ['PATH'] = p + os.pathsep + cur if cur else p

    if shutil.which('lake') and shutil.which('lean'):
        return
    # Try common candidates
    home_bin = os.path.join(os.path.expanduser('~'), '.elan', 'bin')
    _add_dir(home_bin)
    if working_root:
        _add_dir(os.path.join(working_root, 'lean-env', 'bin'))
    # Also add typical system bins as fallback
    _add_dir('/usr/local/bin')
    _add_dir('/usr/bin')


def extract_first_code_block(text: str, codeblock_pattern: Pattern[str]) -> str:
    try:
        matches = re.findall(codeblock_pattern, text)
        if matches:
            return matches[0]
        return str(text).strip()
    except Exception:
        return str(text).strip()

