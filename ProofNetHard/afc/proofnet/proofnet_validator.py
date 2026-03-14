# License: Apache 2.0
# pylint: disable=R0903,R0911
# Code Adapted from: https://github.com/loganrjmurphy/LeanEuclid/blob/master/E3/validator.py


# Standard Library Modules
import os
import re
from subprocess import Popen, PIPE, SubprocessError

from loguru import logger

# Internal Modules
from .tools.simplifier import Simplifier, load_relations_content
from ..utils import kill_process_group, merge_lean_sections


VALIDATOR_BASE_HEADER = (
    "import Mathlib\n\n"
    "open Real Complex Filter Function Topology Finset\n"
    "open scoped BigOperators Topology\n"
    "noncomputable section\n"
)

SMT_VALIDATOR_BASE_HEADER = "import Mathlib\nimport Lean\nimport Qq"

OPTIONS = (
    "set_option autoImplicit false\n"
    "set_option linter.unusedVariables false\n"
)

def format_lean_validator_file(theorem: str, relations_content: str = "", header: str = "") -> str:
    merged_header = merge_lean_sections(VALIDATOR_BASE_HEADER, header, relations_content).rstrip()
    sections = [merged_header] if merged_header else []
    sections.extend([
        "set_option autoImplicit false",
        "set_option linter.unusedVariables false",
        theorem.strip(),
    ])
    result = "\n".join(sections)
    return result + ("\n" if not result.endswith("\n") else "")


def remove_imports(theorem: str) -> str:
    # remove all import statements from theorem
    sanitized_lines = [
        line for line in theorem.splitlines() if not line.lstrip().startswith("import ")
    ]
    sanitized_theorem = "\n".join(sanitized_lines).strip()
    return sanitized_theorem

def format_lean_validator_file_no_header(theorem: str, relations_content: str = "") -> str:
    sanitized_theorem = remove_imports(theorem)
    if relations_content:
        sanitized_relations = remove_imports(relations_content)
        return f"import Mathlib\n\n{OPTIONS}\n\n{sanitized_relations}\n\n\n{sanitized_theorem}"

    return f"import Mathlib\n\n{OPTIONS}\n\n{sanitized_theorem}"


class Validator:
    def __init__(
        self,
        root_dir: str,
        tmp_dir: str,
        relations_file: str,
        *,
        quiet: bool = True,
    ) -> None:
        self.root_dir = root_dir
        self.tmp_dir = tmp_dir
        self.relations_file = relations_file
        self.quiet = quiet
        os.makedirs(self.tmp_dir, exist_ok=True)
        # Directory to persist Lean error outputs for debugging/prompt tuning
        self.error_dir = os.path.join(self.tmp_dir, "lean_errors")
        os.makedirs(self.error_dir, exist_ok=True)
        # Initialize the simplifier and checker for validation
        self.simplifier = Simplifier(self.root_dir, self.tmp_dir, self.relations_file, quiet=quiet)
        self.relations_content = load_relations_content(relations_file)
        # No need to set bin_time for "precheck" mode, each pre-check are set to have 5s timeout

    def validate_lean_syntax(self, theorem: str, instance_name: str, header: str = "") -> str | None:
        tmp_file = os.path.join(self.tmp_dir, f"{instance_name}_lean-syntax.lean")

        if header:
            lean_file = format_lean_validator_file(theorem, self.relations_content, header)
        else:
            # print("====================================================")
            # print("No header provided, removing imports from theorem, and append it to the relations file")
            # print("====================================================")
            lean_file = format_lean_validator_file_no_header(theorem, self.relations_content)

        with open(tmp_file, "w", encoding="utf-8") as file:
            file.write(lean_file)

        # Set up the command to run the validator with proper Lean environment
        lean_env_dir = os.path.join(self.root_dir, "lean-env", "mathlib4")
        command = ["lake", "env", "lean", tmp_file]

        process: Popen[str] | None = None
        try:
            with Popen(
                command,
                stdin=PIPE,
                stdout=PIPE,
                cwd=lean_env_dir,
                start_new_session=True,
                text=True,
                encoding="utf-8",
                close_fds=True,
            ) as process:
                stdout, stderr = process.communicate()

                if stderr:
                    stderr = stderr.strip()
                    if not self.quiet:
                        logger.warning(f"Validator warning(s) for {tmp_file}: {stderr}")

                # extract the error message from stdout
                error = None
                if stdout:
                    # Remove the file path from the error message
                    # First try the standard format with line:column
                    error = re.sub(r"/[^:]+:\d+:\d+: ", "", stdout)
                    # Then, try a more general pattern to without line:column numbers
                    error = re.sub(r"/[^\n]*?(?=(?:error|warning):\s?)", "", error, flags=re.MULTILINE)
                    error = error.strip()

                    # Special handling for 'sorry' warnings - treat them as success
                    if error and "uses 'sorry'" in error:
                        if not self.quiet:
                            logger.info("Lean syntax is valid (uses 'sorry' for proof)")
                        error = None
                # Persist error artifacts to help prompt tuning
                try:
                    base = os.path.splitext(os.path.basename(tmp_file))[0]
                    if stdout:
                        with open(os.path.join(self.error_dir, f"{base}.stdout.txt"), "w", encoding="utf-8") as f_out:
                            f_out.write(stdout)
                    if stderr:
                        with open(os.path.join(self.error_dir, f"{base}.stderr.txt"), "w", encoding="utf-8") as f_err:
                            f_err.write(stderr)
                    if error:
                        with open(os.path.join(self.error_dir, f"{base}.error.txt"), "w", encoding="utf-8") as f_msg:
                            f_msg.write(error)
                        # Also write a machine-friendly classification for downstream summarization
                        try:
                            meta = self._classify_error(error)
                            import json as _json
                            with open(os.path.join(self.error_dir, f"{base}.error.json"), "w", encoding="utf-8") as f_meta:
                                _json.dump(meta, f_meta, ensure_ascii=False, indent=2)
                        except Exception:
                            pass
                except OSError:
                    # Do not fail validation on logging errors
                    pass
                return error

        except (SubprocessError, OSError) as e:
            if not self.quiet:
                logger.error(f"Failed to execute validator: {e}")
            return "validation_error"
        except Exception as e:
            if not self.quiet:
                logger.error(f"Unexpected error {type(e).__name__}: {e}")
            return "unexpected_error"
        finally:
            if process and process.pid:
                kill_process_group(process.pid)

    @staticmethod
    def _classify_error(msg: str) -> dict:
        """Classify a Lean error message into coarse categories for ProofNet.

        Returns a dict with fields: category, tokens (optional), raw.
        """
        import re as _re
        s = msg or ""
        s_low = s.lower()
        meta = {"category": "unknown", "raw": s}
        # Patterns
        m = _re.search(r"unknown identifier '([^']+)'", s)
        if m:
            meta.update({"category": "unknown_identifier", "tokens": [m.group(1)]}); return meta
        m = _re.search(r"unknown constant '([^']+)'", s)
        if m:
            meta.update({"category": "unknown_constant", "tokens": [m.group(1)]}); return meta
        if "failed to synthesize instance" in s_low:
            meta.update({"category": "instance_synthesis_failed"}); return meta
        if "application type mismatch" in s_low:
            meta.update({"category": "application_type_mismatch"}); return meta
        if _re.search(r"^error: type mismatch", s, flags=_re.MULTILINE):
            meta.update({"category": "type_mismatch"}); return meta
        if "ambiguous, possible interpretations" in s:
            meta.update({"category": "ambiguous"}); return meta
        if "invalid field notation" in s_low:
            meta.update({"category": "invalid_field_notation"}); return meta
        if _re.search(r"unexpected token|expected token", s_low):
            meta.update({"category": "parse_error"}); return meta
        if "typeclass instance problem is stuck" in s_low:
            meta.update({"category": "typeclass_stuck"}); return meta
        if "invalid field '" in s:
            meta.update({"category": "invalid_field"}); return meta
        return meta


    def validate_smt_translation(self, theorem: str, instance_name: str, header: str = "") -> str | None:
        # Check if this is a ProofNet theorem
        is_proofnet = any(keyword in theorem for keyword in ["Set ℂ", "ℂ → ℂ", "DifferentiableOn", "IsOpen"])

        if is_proofnet:
            # For ProofNet, skip SMT translation validation since it's complex
            # and not necessary for basic theorem validation
            if not self.quiet:
                logger.info("Skipping SMT translation validation for ProofNet theorem")
            return None

        tmp_file = os.path.join(self.tmp_dir, f"{instance_name}_smt-translation.lean")

        lean_file = format_smt_validator_file(theorem, self.relations_content, header)
        with open(tmp_file, "w", encoding="utf-8") as file:
            file.write(lean_file)

        # Set up the command to run the validator
        command = ["lake", "env", "lean", "--run", tmp_file]

        process: Popen[str] | None = None
        try:
            with Popen(
                command,
                stdin=PIPE,
                stdout=PIPE,
                cwd=self.root_dir,
                start_new_session=True,
                text=True,
                encoding="utf-8",
                close_fds=True,
            ) as process:
                stdout, stderr = process.communicate()

                if stderr:
                    stderr = stderr.strip()
                    if not self.quiet:
                        logger.warning(f"Validator warning(s) for {tmp_file}: {stderr}")

                # extract the error message from stdout
                error = None
                if stdout:
                    # Remove the file path from the error message
                    # First try the standard format with line:column
                    error = re.sub(r"/[^:]+:\d+:\d+: ", "", stdout)
                    # Then, try a more general pattern to without line:column numbers
                    error = re.sub(r"/[^\n]*?(?=(?:error|warning):\s?)", "", error, flags=re.MULTILINE)
                    error = error.strip()

                    # Special handling for 'sorry' warnings - treat them as success
                    if error and "uses 'sorry'" in error:
                        if not self.quiet:
                            logger.info("SMT translation is valid (uses 'sorry' for proof)")
                        error = None
                # Persist error artifacts to help prompt tuning
                try:
                    base = os.path.splitext(os.path.basename(tmp_file))[0]
                    if stdout:
                        with open(os.path.join(self.error_dir, f"{base}.stdout.txt"), "w", encoding="utf-8") as f_out:
                            f_out.write(stdout)
                    if stderr:
                        with open(os.path.join(self.error_dir, f"{base}.stderr.txt"), "w", encoding="utf-8") as f_err:
                            f_err.write(stderr)
                    if error:
                        with open(os.path.join(self.error_dir, f"{base}.error.txt"), "w", encoding="utf-8") as f_msg:
                            f_msg.write(error)
                except OSError:
                    # Do not fail validation on logging errors
                    pass
                return error

        except (SubprocessError, OSError) as e:
            if not self.quiet:
                logger.error(f"Failed to execute validator: {e}")
            return "validation_error"
        except Exception as e:
            if not self.quiet:
                logger.error(f"Unexpected error {type(e).__name__}: {e}")
            return "unexpected_error"
        finally:
            if process and process.pid:
                kill_process_group(process.pid)

    def validate(self, theorem: str, instance_name: str, header: str = "") -> str | None:
        # Step 1: Check if the theorem is syntactically valid in Lean
        if not self.quiet:
            logger.info("STEP 1: Validate Lean Syntax")
        # Use a single tmp filename pattern "<idx>_lean-syntax.lean" to avoid duplicates
        error = self.validate_lean_syntax(theorem, instance_name, header)
        if error is None:
            if not self.quiet:
                logger.info("Lean syntax is valid")
        else:
            if not self.quiet:
                logger.error(f"Lean syntax violation: {error}")
            return error

        return None


def main() -> None:
    """Test the validator with example theorems."""
    # Parallel Thm03
    theorem_1 = (  # noqa: F841
        "∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ "
        "distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ twoLinesIntersectAtPoint UW QX V ∧ "
        "between U V W ∧ sequentiallyAlignedList [Q, S, V, X] ∧ sameSideDistinctList [R, U] QX ∧ sameSideDistinctList [T, W] QX ∧ "
        "∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT"
    )
    problem_text_1 = (
        "Lines UW and QX intersect at V. RT and QX intersect at S. The points X, V, S, and Q are sequentially aligned. "
        "The set of points U, R and the set of points T, W are on opposing sides of the line QX.\n\n"
        "Given ∠ T S V and ∠ S V W are supplementary. Complete the proof that U W ∥ R T."
    )
    # Congruent Thm02
    theorem_2 = (  # noqa: F841
        "∀ (T U V W : Point) (UV TW UT VW VT : Line), formConvexQuadrilateral U V T W UV TW UT VW ∧ distinctPointsOnLine V T VT ∧ "
        "formTriangle U V T UV VT UT ∧ formTriangle V W T VW TW VT ∧ |(T─U)| = |(V─W)| ∧ ¬ UT.intersectsLine VW "
        "→ (△ T:U:V).congruent (△ V:W:T)"
    )
    # Contradictory Premises
    theorem_2_variant_1 = (  # noqa: F841
        "∀ (T U V W : Point) (UV TW UT VW VT : Line), formConvexQuadrilateral U V T W UV TW UT VW ∧ distinctPointsOnLine V T VT ∧ "
        "formTriangle U V T VT UV UT ∧ formTriangle V W T VW TW VT ∧ |(T─U)| = |(V─W)| ∧ ¬ UT.intersectsLine VW "
        "→ (△ T:U:V).congruent (△ V:W:T)"
    )
    # Valid Conclusion
    theorem_2_variant_2 = (  # noqa: F841
        "∀ (T U V W : Point) (UV TW UT VW VT : Line), formConvexQuadrilateral U V T W UV TW UT VW ∧ distinctPointsOnLine V T VT ∧ "
        "formTriangle U V T UV VT UT ∧ formTriangle V W T VW TW VT ∧ |(T─U)| = |(V─W)| ∧ ¬ UT.intersectsLine VW "
        "→  (T = U ∧ U = W → T = W)"
    )
    # False Statement
    theorem_2_variant_3 = "∀ (T U V : Point),  T = U ∧ U = V → T ≠ V"  # noqa: F841
    problem_text_2 = (
        "There is a convex quadrilateral UVTW with a diagonal line VT, which divides the quadrilateral into two triangles, △UVT and △VWT.\n\n"
        "Given T U ≅ V W. T U ∥ V W. Complete the proof that △ T U V ≅ △ V W T."
    )
    test_list = [
        (theorem_1, problem_text_1),
        (theorem_2, problem_text_2),
        (theorem_2_variant_1, problem_text_2),
        (theorem_2_variant_2, problem_text_2),
        (theorem_2_variant_3, problem_text_2),
    ]

    # Set up directories
    root_dir = os.path.abspath("LeanEuclid_Customized")
    tmp_dir = os.path.join(
        root_dir,
        "tmp",
        "validate",
        "test_validator",
    )
    os.makedirs(tmp_dir, exist_ok=True)
    logger.info(f"Using temporary directory: {tmp_dir}")

    # Create Validator instance
    validator = Validator(root_dir=root_dir, tmp_dir=tmp_dir, relations_file="Relations_oracle", quiet=False)

    logger.info("🔬 Testing LeanEuclid Validator")
    logger.info("=" * 80)

    for idx, (theorem, problem_text) in enumerate(test_list):
        logger.info("📝 Original theorem with composite relations:")
        logger.info("-" * 80)
        logger.info(theorem)
        logger.info("=" * 80)

        # Test validation
        logger.info("🚀 Running validation...")
        error = validator.validate(theorem, problem_text, f"test_{idx}")

        if error is None:
            logger.info("✅ Validation passed!")
        else:
            logger.info("❌ Validation failed")
        logger.info("=" * 80)


if __name__ == "__main__":
    main()
