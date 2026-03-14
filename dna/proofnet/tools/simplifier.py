
# License: Apache 2.0
# pylint: disable=R0903

import os
import re
from subprocess import Popen, PIPE, SubprocessError

from loguru import logger

from ...utils import kill_process_group, merge_lean_sections


DEFAULT_SIMPLIFIER_HEADER = (
    "import Mathlib\n\n"
    "open Real Complex Filter Function Topology Finset\n"
    "open scoped BigOperators Topology\n"
    "noncomputable section\n\n"
    "universe u v w u_1 u_2 u_3 v_1 v_2 w_1 w_2\n"
)


def load_relations_content(relations_file: str) -> str:
    if not relations_file or not isinstance(relations_file, str):
        return ""
    try:
        if os.path.isfile(relations_file):
            with open(relations_file, "r", encoding="utf-8") as handle:
                return handle.read()
    except OSError:
        pass
    return ""


def format_lean_validation_file(theorem: str, *, header: str = "", relations: str = "") -> str:
    """Format a temporary Lean file to validate ProofNet/DSL theorems."""
    merged_header = merge_lean_sections(DEFAULT_SIMPLIFIER_HEADER, header, relations).rstrip()
    if merged_header:
        merged_header += "\n\n"
    return f"{merged_header}{theorem}\n"


class Simplifier:
    """Simplifier class for converting composite relations to primitive relations."""

    def __init__(self, root_dir: str, tmp_dir: str, relations_file: str, *, quiet: bool = False) -> None:
        self.root_dir = root_dir
        self.tmp_dir = tmp_dir
        self.relations_file = relations_file
        self.quiet = quiet
        os.makedirs(self.tmp_dir, exist_ok=True)
        self.relations_content = load_relations_content(relations_file)

    def _log(self, level: str, message: str) -> None:
        if self.quiet:
            return
        log_fn = getattr(logger, level, logger.info)
        log_fn(message)

    def simplify(
        self,
        theorem: str,
        instance_name: str = "temp_simplify",
        header: str = "",
    ) -> str | tuple[None, str]:
        """Simplify a theorem by converting composite relations to primitive relations.

        Returns simplified theorem, or (None, error) if failed.
        """
        try:
            self._log("info", "ℹ️  ProofNet theorem detected - using simplified validation")
            tmp_file = os.path.join(self.tmp_dir, f"{instance_name}.lean")

            if os.path.isfile(tmp_file):
                try:
                    os.remove(tmp_file)
                    self._log("info", f"🔨 Removed old tmp file {tmp_file}")
                except OSError as e:
                    self._log("warning", f"⚠️  Failed to remove old tmp file {tmp_file}: {e}")

            lean_content = format_lean_validation_file(theorem, header=header, relations=self.relations_content)
            with open(tmp_file, "w", encoding="utf-8") as file:
                file.write(lean_content)
                self._log("info", f"🔨 Created ProofNet validation file {tmp_file}")

            command = ["lake", "env", "lean", tmp_file]

            process: Popen[str] | None = None
            try:
                with Popen(
                    command,
                    stdout=PIPE,
                    stderr=PIPE,
                    cwd=os.path.join(self.root_dir, "lean-env", "mathlib4"),
                    start_new_session=True,
                    text=True,
                    encoding="utf-8",
                    close_fds=True,
                ) as process:
                    stdout, stderr = process.communicate()

                    if stderr:
                        stderr = stderr.strip()
                        self._log("warning", f"❗ ProofNet Validation Warning(s) for {tmp_file}: {stderr}")

                    if stdout and ("error" in stdout.lower() or "unexpected" in stdout.lower()):
                        error = re.sub(r"/[^:]+:\d+:\d+: ", "", stdout)
                        error = re.sub(r"/[^\n]*?(?=(?:error|warning):\s?)", "", error, flags=re.MULTILINE)
                        error = error.strip()
                        self._log("warning", f"❌ Validation failed: {error}")
                        return None, error

                    return theorem  # Valid as-is

            except (SubprocessError, OSError) as e:
                self._log("error", f"⚠️  Failed to execute lake build: {e}")
                return None, f"Failed to execute lake build: {e}"
            except Exception as e:
                self._log("error", f"⚠️  Unexpected error {type(e).__name__}: {e}")
                return None, f"Unexpected error {type(e).__name__}: {e}"
            finally:
                if process and process.pid:
                    kill_process_group(process.pid)

        except Exception as e:
            print(f"⚠️  Unexpected error before lake build: {type(e).__name__}: {e}")
            return None, f"Unexpected error before lake build: {type(e).__name__}: {e}"
