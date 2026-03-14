 
# License: Apache 2.0
# pylint: disable=R0903,R0911
# Code Adapted from: https://github.com/loganrjmurphy/LeanEuclid/blob/master/E3/validator.py


# Standard Library Modules
import os
import re
from subprocess import Popen, PIPE, SubprocessError

# Internal Modules
from .leaneuclid_simplifier import Simplifier, extract_variables_from_theorem
from .leaneuclid_checker import EquivalenceChecker
from ..utils import kill_process_group


def format_lean_theorem_file(theorem: str, relations_file: str) -> str:
    return f"""import UniGeo.{relations_file}

set_option autoImplicit false
set_option linter.unusedVariables false

def test : Prop := {theorem}
"""


def format_smt_translation_file(test: str, relations_file: str) -> str:
    return f"""import SystemE
import UniGeo.{relations_file}
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def testE : Expr := q({test})

def main : IO Unit := WfChecker testE
"""


class Validator:
    def __init__(
        self,
        root_dir: str,
        tmp_dir: str,
        relations_file: str,
    ) -> None:
        self.root_dir = root_dir
        self.tmp_dir = tmp_dir
        self.relations_file = relations_file
        os.makedirs(self.tmp_dir, exist_ok=True)
        # Initialize the simplifier and checker for validation
        self.simplifier = Simplifier(self.root_dir, self.tmp_dir, self.relations_file)
        # No need to set bin_time for "precheck" mode, each pre-check are set to have 5s timeout
        self.checker = EquivalenceChecker(
            self.root_dir,
            self.tmp_dir,
            self.tmp_dir,
            self.relations_file,
            self.relations_file,
            "precheck",
            # No need to simplify ground and test, since we will run simplification before the pre-checks
            skip_simp=True,
        )

    def validate_lean_file(
        self,
        lean_file: str,
        instance_name: str,
        command_prefix: list[str] | None = None,
        suffix: str = "entire-file",
    ) -> str | None:
        tmp_file = os.path.join(self.tmp_dir, f"{instance_name}_{suffix}.lean")
        with open(tmp_file, "w", encoding="utf-8") as file:
            file.write(lean_file)

        # Set up the command to run the validator
        # Default command is ["lake", "env", "lean", tmp_file]
        default_prefix = ["lake", "env", "lean"]
        command = (command_prefix or default_prefix) + [tmp_file]

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
                    print("+" * 60)
                    print(f"❗ Validator Warning(s) for {tmp_file}:", end=" ")
                    print(stderr)
                    print("+" * 60)

                # extract the error message from stdout
                error = None
                if stdout:
                    # Remove the file path from the error message
                    # First try the standard format with line:column
                    error = re.sub(r"/[^:]+:\d+:\d+: ", "", stdout)
                    # Then, try a more general pattern to without line:column numbers
                    error = re.sub(r"/[^\n]*?(?=(?:error|warning):\s?)", "", error, flags=re.MULTILINE)
                    error = error.strip()
                return error

        except (SubprocessError, OSError) as e:
            print(f"⚠️  Failed to execute validator: {e}")
            return "validation_error"
        except Exception as e:
            print(f"⚠️  Unexpected error {type(e).__name__}: {e}")
            return "unexpected_error"
        finally:
            if process and process.pid:
                kill_process_group(process.pid)

    def validate_lean_theorem_syntax(self, theorem: str, instance_name: str) -> str | None:
        # Construct the Lean file for theorem syntax validation
        lean_file = format_lean_theorem_file(theorem, self.relations_file)
        # Validate the Lean file
        command_prefix = ["lake", "env", "lean"]
        return self.validate_lean_file(lean_file, instance_name, command_prefix, suffix="lean-syntax")

    def validate_variable_names(self, theorem: str, problem_text: str) -> str | None:
        result = extract_variables_from_theorem(theorem)
        # If the result is a string, it means there is an error in the theorem
        if isinstance(result, str):
            return result
        point_names, line_names, circle_names = result

        for point_name in point_names:
            # For point names, it must be a single character
            if len(point_name) != 1:
                return f"Variable naming violation! Your point name: {point_name} is not exactly one character."
            # It must exist in the problem text
            if point_name not in problem_text:
                return f"Variable naming violation! Your point name: {point_name} cannot be found in English problem statement."

        for line_name in line_names:
            # For line names, it must be exactly 2 characters representing the two points on the line
            if len(line_name) != 2:
                return f"Variable naming violation! Your line name: {line_name} is not exactly 2 characters representing the two points on the line."
            # There might be some lines that are only implicitly mentioned in the English problem text,
            # for example, "There are two triangles △RUP and △TQP with a shared vertex at P.",
            # which defines 6 lines: RU, UP, RP, TQ, TP, and PQ without explicitly mentioning them.
            # Therefore, there is no good way to check if the line name is in the problem text without overfitting to certain syntactic patterns.

        for circle_name in circle_names:
            # UniGeo problem statement does not contain circle names
            if circle_names:
                return f"Variable naming violation! Your circle name: {circle_name} cannot be found in English problem statement."

        return None

    def validate_smt_translation(self, theorem: str, instance_name: str) -> str | None:
        # Construct the Lean file for SMT translation validation
        lean_file = format_smt_translation_file(theorem, self.relations_file)
        # Validate the Lean file
        command_prefix = ["lake", "env", "lean", "--run"]
        return self.validate_lean_file(lean_file, instance_name, command_prefix, suffix="smt-translation")

    def validate(self, theorem: str, problem_text: str, instance_name: str) -> str | None:
        # Step 1: Check if the theorem is syntactically valid in Lean
        print("STEP 1: Validate Lean Syntax")
        error = self.validate_lean_theorem_syntax(theorem, f"{instance_name}_lean-syntax")
        if error is None:
            print("✅ Lean Syntax is Valid")
        else:
            print(f"❌ Lean Syntax Violation: {error}")
            return error
        print("-" * 80)

        # Step 2: Check if variable names are in the English statement
        print("STEP 2: Check if variable names are in the English statement")
        error = self.validate_variable_names(theorem, problem_text)
        if error is None:
            print("✅ Variable Naming is Valid")
        else:
            print(f"❌ Variable Naming Violation: {error}")
            return error
        print("-" * 80)

        # Step 3: If passed, simplify the theorem
        print("STEP 3: Simplify the theorem")
        simplified_theorem = self.simplifier.simplify(theorem, f"{instance_name}_simplify")
        if isinstance(simplified_theorem, str):
            print("✅ Simplification Succeeded")
        else:
            assert (
                isinstance(simplified_theorem, tuple) and simplified_theorem[0] is None
            ), f"Unexpected simplified theorem {self.tmp_dir}/{instance_name}, expected a tuple[None, str], got {simplified_theorem}"
            print(f"❌ Simplification Error: {simplified_theorem[1]}")
            return simplified_theorem[1]
        print("-" * 80)

        # Step 4: Check if the simplified theorem is supported by the SMT translator
        print("STEP 4: Validate SMT Translation")
        error = self.validate_smt_translation(simplified_theorem, f"{instance_name}_smt-translation")
        if error is None:
            print("✅ SMT Translation is Valid")
        else:
            print(f"❌ SMT Translation Violation: {error}")
            return error
        print("-" * 80)

        # Step 5: Check if the simplified theorem pass the pre-checks
        # Pre-check 1 - Checking if the Test premises is contradictory
        # Pre-check 2 - Checking if the Test conclusions is valid
        # Pre-check 3 - Checking if Test is a false statement
        print("STEP 5: Check if the simplified theorem pass the pre-checks")
        # No need to pass a ground statement, since we are in pre-check mode
        final_result, checker_result, _ = self.checker.check("", simplified_theorem, f"{instance_name}_precheck")
        if final_result == "precheck_passed":
            print("✅ Pre-checks Passed")
        else:
            assert (
                isinstance(checker_result, str) or checker_result is False
            ), f"Unexpected checker_result from 'precheck' mode for {self.tmp_dir}/{instance_name}, expected a str or False, got {checker_result}"
            print(f"❌ Pre-checks Failed: {checker_result}")
            # Return the error message
            if checker_result is False:
                return "Checker error when extracting quantified variables from premises and conclusions in precheck mode"
            return checker_result
        print("-" * 80)

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
    print(f"🔨 Using temporary directory: {tmp_dir}")

    # Create Validator instance
    validator = Validator(root_dir=root_dir, tmp_dir=tmp_dir, relations_file="Relations_oracle")

    print("🔬 Testing LeanEuclid Validator")
    print("=" * 80)

    for idx, (theorem, problem_text) in enumerate(test_list):
        print("📝 Original theorem with composite relations:")
        print("-" * 80)
        print(theorem)
        print("=" * 80)

        # Test validation
        print("🚀 Running validation...")
        error = validator.validate(theorem, problem_text, f"test_{idx}")

        if error is None:
            print("✅ Validation passed!")
        else:
            print("❌ Validation failed")
        print("=" * 80)


if __name__ == "__main__":
    main()
