# License: Apache 2.0
# pylint: disable=R0902,R0912,R1702
# Code Adapted from: https://github.com/loganrjmurphy/LeanEuclid/blob/master/E3/checker.py


# Standard Library Modules
import json
import os
from subprocess import Popen, PIPE, SubprocessError
from typing import Literal

# Internal Modules
from .leaneuclid_simplifier import Simplifier
from ..utils import kill_process_group


def format_lean_checker_file(ground: str, test: str) -> str:
    """Format a Lean checker file with ground truth and test propositions."""
    return f"""import SystemE
import E3
import Qq

set_option autoImplicit false
set_option linter.unusedVariables false

open Qq Lean

def ground : Prop := {ground}
def test : Prop := {test}
def groundE : Expr := q({ground})
def testE : Expr := q({test})

def main (args : List String) : IO Unit := do
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
"""


class EquivalenceChecker:
    """Checker class for verifying equivalence of geometric propositions."""

    def __init__(
        self,
        root_dir: str,
        tmp_dir: str,
        result_dir: str,
        ground_relations_file: str,
        test_relations_file: str,
        # Mode has to be one of "bvars", "skipApprox", "onlyApprox", "full", "precheck", "naive", "separate", "precheck+separate"
        # "naive" will just check the satisfiability of the test and ground statements (they can be any 2 statements)
        # "separate" will check the equivalence of the premises and conclusions of the test and ground statements separately
        # "precheck" will only validate the test statement for basic sanity
        # (premises not contradictory, conclusions not always true, etc.) - IGNORES ground statement
        # "precheck+separate" will run precheck first, then separate mode if precheck passes
        mode: Literal["bvars", "skipApprox", "onlyApprox", "full", "precheck", "naive", "separate", "precheck+separate"],
        # If True, skip simplification of the ground and test statements
        # Make this True ONLY IF you are sure that the ground and test statements are already simplified!
        # We only set this to True in the ./leaneuclid_validator.py#L59C1-L68C10, since we are passing the simplified test to the precheck mode
        skip_simp: bool = False,
        n_perms: int = 3,  # only for approximation checking
        bin_time: int = 120,  # original LeanEuclid paper uses 60s
        approx_time: int = 5,
    ) -> None:
        self.root_dir = root_dir
        self.tmp_dir = tmp_dir
        self.result_dir = result_dir
        self.ground_relations_file = ground_relations_file
        self.test_relations_file = test_relations_file
        os.makedirs(self.tmp_dir, exist_ok=True)
        os.makedirs(self.result_dir, exist_ok=True)
        self.n_permutations = n_perms
        self.equiv_solver_time = bin_time
        self.approx_solver_time = approx_time
        self.mode = mode
        self.skip_simp = skip_simp
        # Initialize the simplifiers for the ground and test statements
        self.ground_simplifier = Simplifier(self.root_dir, self.tmp_dir, self.ground_relations_file)
        self.test_simplifier = Simplifier(self.root_dir, self.tmp_dir, self.test_relations_file)

    def determine_naive_result(self, assertion: str, negation: str) -> str:
        """Determine result based on assertion and negation values."""
        if assertion.startswith("pre-check_failed"):
            return assertion
        if assertion == "UNSAT":
            return "UNSAT"
        if negation == "UNSAT":
            return "VALID"
        if assertion == "TIMEOUT" and negation == "TIMEOUT":
            return "TIMEOUT"
        return "UNKNOWN"

    def determine_separate_result(self, t2g_assertion: str, t2g_negation: str, g2t_assertion: str, g2t_negation: str) -> str:
        """Determine separate result based on SMT solver results."""
        if t2g_negation == "UNSAT" and g2t_negation == "UNSAT":
            return "VALID"
        if t2g_assertion == "UNSAT" or g2t_assertion == "UNSAT":
            return "UNSAT"
        if t2g_assertion == "TIMEOUT" and g2t_assertion == "TIMEOUT" and t2g_negation == "TIMEOUT" and g2t_negation == "TIMEOUT":
            return "TIMEOUT"
        if t2g_negation == "UNSAT" and g2t_negation == "TIMEOUT":
            return "VALID_t2g"
        if g2t_negation == "UNSAT" and t2g_negation == "TIMEOUT":
            return "VALID_g2t"
        return "UNKNOWN"

    def handle_binary_result(self, full_result: dict) -> str | bool:
        """Handle results for binary only mode"""
        try:
            binary_result: str = full_result["binary_check"]

            # fetch the detailed SMT solver return values
            t2g_assertion = full_result["test_implies_ground"]["assertion"]
            t2g_negation = full_result["test_implies_ground"]["negation"]
            g2t_assertion = full_result["ground_implies_test"]["assertion"]
            g2t_negation = full_result["ground_implies_test"]["negation"]

            # if we got TIMEOUT for both assertion and negation, it is highly likely that that statement is true
            if binary_result == "ground_imp_test" and t2g_assertion == "TIMEOUT" and t2g_negation == "TIMEOUT":
                return "likely_equiv"
            if binary_result == "test_imp_ground" and g2t_assertion == "TIMEOUT" and g2t_negation == "TIMEOUT":
                return "likely_equiv"
            return binary_result

        except KeyError:
            print("⚠️  KeyError in binary result handling.")
            return False

    def handle_naive_result(self, full_result: dict) -> tuple[str, str] | bool:
        """Handle results for naive mode"""
        try:
            naive_result = full_result["naive_check"]

            # Return True if both test and ground have consistent satisfiability
            test_assertion = naive_result["test"]["assertion"]
            test_negation = naive_result["test"]["negation"]
            ground_assertion = naive_result["ground"]["assertion"]
            ground_negation = naive_result["ground"]["negation"]

            test_result = self.determine_naive_result(test_assertion, test_negation)
            ground_result = self.determine_naive_result(ground_assertion, ground_negation)
            return test_result, ground_result

        except KeyError:
            print("⚠️  KeyError in naive result handling.")
            return False

    def handle_separate_result(self, full_result: dict) -> tuple[str, str] | bool:
        """Handle results for separate mode"""
        try:
            separate_result = full_result["separate_check"]

            # Check if both premises and conclusions are equivalent based on detailed SMT results
            premises_t2g_assertion = separate_result["premises"]["test_implies_ground"]["assertion"]
            premises_t2g_negation = separate_result["premises"]["test_implies_ground"]["negation"]
            premises_g2t_assertion = separate_result["premises"]["ground_implies_test"]["assertion"]
            premises_g2t_negation = separate_result["premises"]["ground_implies_test"]["negation"]
            conclusions_t2g_assertion = separate_result["conclusions"]["test_implies_ground"]["assertion"]
            conclusions_t2g_negation = separate_result["conclusions"]["test_implies_ground"]["negation"]
            conclusions_g2t_assertion = separate_result["conclusions"]["ground_implies_test"]["assertion"]
            conclusions_g2t_negation = separate_result["conclusions"]["ground_implies_test"]["negation"]

            premises_result = self.determine_separate_result(
                premises_t2g_assertion, premises_t2g_negation, premises_g2t_assertion, premises_g2t_negation
            )
            conclusions_result = self.determine_separate_result(
                conclusions_t2g_assertion, conclusions_t2g_negation, conclusions_g2t_assertion, conclusions_g2t_negation
            )
            return premises_result, conclusions_result

        except KeyError:
            print("⚠️  KeyError in separate result handling.")
            return False

    def handle_precheck_result(self, full_result: dict) -> str | bool:
        """Handle results for precheck mode"""
        try:
            precheck_result: str = full_result["precheck"]
            return precheck_result
        except KeyError:
            print("⚠️  KeyError in precheck result handling.")
            return False

    def handle_precheck_plus_separate_result(self, full_result: dict) -> tuple[str, str] | str | bool:
        """Handle results for precheck+separate mode"""
        try:
            precheck_plus_separate_result = full_result["precheck_plus_separate_check"]

            # If pre-check not passed, then we just return the pre-check result
            precheck_result: str = precheck_plus_separate_result["precheck"]
            if precheck_result != "passed":
                return precheck_result

            # If pre-check passed, we return the separate check result
            print("📝 Pre-check passed, getting separate check result")
            # `handle_separate_result` takes the parent dict of "separate_check"
            return self.handle_separate_result(precheck_plus_separate_result)

        except KeyError:
            print("⚠️  KeyError in precheck+separate result handling.")
            return False

    def log_binary_result(self, result: str | bool) -> None:
        """Log binary result with appropriate message."""
        if result == "equiv":
            print("✅ The two statements are equivalent.")
        elif result == "likely_equiv":
            print("🔍 The two statements are likely equivalent, manual checking is needed!")
        elif result == "not_equiv":
            print("❌ The two statements are not equivalent.")
        elif result == "ground_imp_test":
            print("❌ Ground statement implies test statement, but not vice versa.")
        elif result == "test_imp_ground":
            print("❌ Test statement implies ground statement, but not vice versa.")
        elif result == "no_conclusion":
            print("❌ No conclusion can be drawn from the statements.")
        else:
            print("⚠️  Error occurred during checking, please check the logs!")

    def combine_naive_results(self, naive_result: tuple[str, str]) -> str:
        """Combine naive premises and conclusions results into a single result."""
        test_result, ground_result = naive_result
        if test_result == ground_result:
            return "likely_equiv"
        return "not_equiv"

    def combine_separate_results(self, separate_result: tuple[str, str]) -> str:
        """Combine separate premises and conclusions results into a single result."""
        premises_result, conclusions_result = separate_result
        if premises_result == "VALID" and conclusions_result == "VALID":
            combined_result = "equiv"
            print("✅ Both premises and conclusions are equivalent.")
        elif premises_result == "UNSAT" or conclusions_result == "UNSAT":
            combined_result = "not_equiv"
            print("❌ Either premises or conclusions are not equivalent.")
        elif (premises_result in ("VALID_t2g", "VALID_g2t") and conclusions_result == "VALID") or (
            premises_result == "VALID" and conclusions_result in ("VALID_t2g", "VALID_g2t")
        ):
            combined_result = "likely_equiv"
            print("🔍 Likely equivalent, manual checking needed!")
        else:
            combined_result = "no_conclusion"
            print("❌ No conclusion can be drawn from the premises and conclusions.")

        return combined_result

    def check(self, ground: str, test: str, instance_name: str) -> tuple[str, str | bool | tuple[str, str], dict]:
        """Synchronous version of check for multiprocessing

        Note: In "precheck" mode, only the test statement is analyzed; ground statement is ignored.
        """
        # clean up old Lean and result files
        tmp_file = os.path.join(self.tmp_dir, instance_name + ".lean")
        output_json_file = os.path.join(self.result_dir, instance_name + ".json")
        output_log_file = os.path.join(self.result_dir, instance_name + ".txt")

        if os.path.isfile(tmp_file):
            try:
                os.remove(tmp_file)
                print(f"🔨 Removed old tmp file {tmp_file}")
            except OSError as e:
                print(f"⚠️  Failed to remove old tmp file {tmp_file}: {e}")

        if os.path.isfile(output_json_file):
            try:
                os.remove(output_json_file)
                print(f"🔨 Removed old json file {output_json_file}")
            except OSError as e:
                print(f"⚠️  Failed to remove old json file {output_json_file}: {e}")

        if os.path.isfile(output_log_file):
            try:
                os.remove(output_log_file)
                print(f"🔨 Removed old log file {output_log_file}")
            except OSError as e:
                print(f"⚠️  Failed to remove old log file {output_log_file}: {e}")

        # Simplify the ground and test statements
        # ground is not needed in the "precheck" mode, since we are only checking the test statement,
        # so we use a placeholder statement as `simplified_ground`
        if self.mode == "precheck":
            simplified_ground: str | tuple[None, str] = "∀ (A : Point), A = A"
        elif self.skip_simp:
            simplified_ground = ground
        else:
            simplified_ground = self.ground_simplifier.simplify(ground, f"{instance_name}_ground_simplify")
            print("-" * 80)
        # test will always be simplified unless `skip_simp` is set True
        if self.skip_simp:
            simplified_test: str | tuple[None, str] = test
        else:
            simplified_test = self.test_simplifier.simplify(test, f"{instance_name}_test_simplify")
        print("-" * 80)
        # Assert that simplification is successful
        assert isinstance(simplified_ground, str), f"⚠️  Unexpected error simplifying ground truth: {simplified_ground}"
        assert isinstance(simplified_test, str), f"⚠️  Unexpected error simplifying model predication: {simplified_test}"

        # write the tmp Lean file
        with open(tmp_file, "w", encoding="utf-8") as file:
            lean_file = format_lean_checker_file(simplified_ground, simplified_test)
            file.write(lean_file)
            print(f"🔨 Created new file {tmp_file}")

        # Set up the command to run the checker
        command = [
            "lake",
            "env",
            "lean",
            "--run",
            tmp_file,
            instance_name,
            self.mode,
            str(self.n_permutations),
            str(self.equiv_solver_time),
            str(self.approx_solver_time),
            "true",
            output_json_file,
        ]

        process: Popen[str] | None = None
        try:
            with Popen(
                command,
                stdout=PIPE,
                stderr=PIPE,
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
                    print(f"❗ Checker Warning(s) for {output_json_file}:", end=" ")
                    print(stderr)
                    print("+" * 60)
                if stdout:
                    stdout = stdout.strip()
                    print(stdout)
                # save the stderr & stdout check log to a .txt file
                with open(output_log_file, "w", encoding="utf-8") as f:
                    f.write(stderr)
                    f.write(stdout)

                try:
                    with open(output_json_file, "r", encoding="utf-8") as f:
                        data = json.load(f)
                    print(f"🔨 Created new file {output_json_file}")
                    full_result = data[instance_name]

                    print(f"🔨 Full result: {full_result}")

                    # Construct checker_result
                    checker_result: bool | str | tuple[str, str]
                    if self.mode == "skipApprox":
                        checker_result = self.handle_binary_result(full_result)
                    elif self.mode == "naive":
                        checker_result = self.handle_naive_result(full_result)
                    elif self.mode == "separate":
                        checker_result = self.handle_separate_result(full_result)
                    elif self.mode == "precheck":
                        checker_result = self.handle_precheck_result(full_result)
                    elif self.mode == "precheck+separate":
                        checker_result = self.handle_precheck_plus_separate_result(full_result)
                    else:
                        raise ValueError(f"Unknown mode: {self.mode}")

                    # Construct final_result based on checker_result
                    final_result: str
                    if checker_result is False:
                        print("⚠️  Error occurred during checking, please check the logs!")
                        final_result = "checking_error"
                    elif self.mode == "skipApprox":
                        assert isinstance(checker_result, str), "Expected result to be a string in binary or naive mode"
                        self.log_binary_result(checker_result)
                        final_result = checker_result
                    elif self.mode == "naive":
                        assert isinstance(checker_result, tuple), "Expected result to be a tuple in naive mode"
                        final_result = self.combine_naive_results(checker_result)
                    elif self.mode == "separate":
                        assert isinstance(checker_result, tuple), "Expected result to be a tuple in separate mode"
                        final_result = self.combine_separate_results(checker_result)
                    elif self.mode == "precheck":
                        assert isinstance(checker_result, str), "Expected result to be a string in precheck mode"
                        if checker_result == "passed":
                            final_result = "precheck_passed"
                        # If pre-check failed, there is no way that test is equivalent to ground
                        else:
                            final_result = "not_equiv"
                    elif self.mode == "precheck+separate":
                        assert isinstance(checker_result, (tuple, str)), "Result should be a tuple of strings, or a string in precheck+separate mode"
                        # if the result is a string, it means pre-check failed
                        if isinstance(checker_result, str):
                            final_result = "not_equiv"
                        # otherwise, the result is a tuple of strings, which means the pre-check passed
                        # we need to combine the results of the separate check
                        else:
                            final_result = self.combine_separate_results(checker_result)
                    else:
                        raise ValueError(f"Unknown mode: {self.mode}")

                    # Add the checker_result, final_result to the output json file
                    with open(output_json_file, "r", encoding="utf-8") as f:
                        data = json.load(f)
                    data[instance_name]["checker_result"] = checker_result
                    data[instance_name]["final_result"] = final_result
                    with open(output_json_file, "w", encoding="utf-8") as f:
                        json.dump(data, f, indent=4, ensure_ascii=False)
                    print("-" * 60)
                    print(f"📝 Checker Result: {checker_result}")
                    print(f"📝 Final Result: {final_result}")
                    print("-" * 60)

                    return final_result, checker_result, full_result

                except (FileNotFoundError, json.JSONDecodeError, KeyError) as e:
                    print(f"⚠️  Failed to parse output file: {e}")
                    return "checking_error", False, {}

        except (SubprocessError, OSError) as e:
            print(f"⚠️  Failed to execute checker: {e}")
            return "checking_error", False, {}
        except Exception as e:
            print(f"⚠️  Unexpected error {type(e).__name__}: {e}")
            return "checking_error", False, {}
        finally:
            if process and process.pid:
                kill_process_group(process.pid)


def main() -> None:
    """Test the validator with example theorems."""
    # Example theorem from DSL_Parallel_Thm03.lean
    test_1 = (  # noqa: F841
        "∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ "
        "distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ "
        "twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ sequentiallyAlignedList [Q, S, V, X] ∧ sameSideDistinctList [R, U] QX ∧ "
        "sameSideDistinctList [T, W] QX ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT"
    )
    ground_1 = (  # noqa: F841
        "∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ "
        "distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ "
        "between Q S V ∧ twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧ R.sameSide U QX ∧ R ≠ U ∧ "
        "T.sameSide W QX ∧ T ≠ W ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT"
    )

    test_list = [(ground_1, test_1)]

    # Set up directories
    root_dir = os.path.abspath("LeanEuclidPlus")
    tmp_dir = os.path.join(
        root_dir,
        "tmp",
        "check",
        "test_checker",
    )
    os.makedirs(tmp_dir, exist_ok=True)
    print(f"🔨 Using temporary directory: {tmp_dir}")

    # Create EquivalenceChecker instance
    checker = EquivalenceChecker(
        root_dir=root_dir,
        tmp_dir=tmp_dir,
        result_dir=tmp_dir,
        ground_relations_file="Relations",
        test_relations_file="Relations_oracle",
        mode="precheck+separate",
    )

    print("🔬 Testing LeanEuclid Equivalence Checker")
    print("=" * 80)

    for idx, (ground, test) in enumerate(test_list):
        print("📝 Original theorem with composite relations:")
        print("-" * 80)
        print(f"Ground: {ground}")
        print("-" * 80)
        print(f"Test: {test}")
        print("=" * 80)

        # Test Equivalence Checker
        print("🚀 Running equivalence checking...")
        final_result, checker_result, full_result = checker.check(ground, test, f"test_{idx}")

        if final_result == "equiv":
            print("✅ Equivalence checking passed!")
        else:
            print(f"❌ Equivalence checking failed: {final_result}")
        print(checker_result)
        print(full_result)
        print("=" * 80)


if __name__ == "__main__":
    main()
