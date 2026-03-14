# License: Apache 2.0
# pylint: disable=R0903,R0911


# Standard Library Modules
import os
import re
from subprocess import Popen, PIPE, SubprocessError

# Internal Modules
from ..utils import kill_process_group


def format_lean_simplifier_file(theorem: str, relations_file: str, variable_names: list[str]) -> str:
    """Format a temporary Lean file to simplify composite relations to primitive ones.

    The `intro` tactic must follow the original binder order so that each name is
    introduced with the correct type. Otherwise Lean will associate the wrong type
    with a variable, leading to malformed simplified statements (for example, lines
    being treated as circles).
    """
    # Maintain the original quantifier order to respect Lean's binder types
    all_vars = " ".join(variable_names + ["h"])

    return f"""import UniGeo.{relations_file}

set_option autoImplicit false
set_option linter.unusedVariables false

#guard_msgs(drop warning) in
theorem simplify_theorem : {theorem} := by
  intro {all_vars}
  try simp at h  -- Try to simplify premises
  try simp       -- Try to simplify conclusion
  trace_state
  sorry
"""


def extract_variables_from_theorem(theorem: str) -> str | tuple[list[str], list[str], list[str], list[str]]:
    """Extract point, line, and circle variable names from a theorem string.

    Returns:
        str | tuple[list[str], list[str], list[str], list[str]]: A tuple containing
        the point names, line names, circle names, and the original binder order.
    """
    # Pattern to match the universal quantification part
    # Handle different patterns:
    # 1. "∀ (A : Point), ..." - only points
    # 2. "∀ (AB : Line), ..." - only lines
    # 3. "∀ (a b c : Circle), ..." - only circles
    # 4. "∀ (A B : Point) (AB CD : Line), ..." - points and lines
    # 5. "∀ (a b c : Circle) (AB BC AC : Line), ..." - circles and lines
    # 6. "∀ (A B : Point) (a b c : Circle) (AB BC AC : Line), ..." - all three types

    # First, extract everything between ∀ and the first comma
    quantification_pattern = r"∀\s*(.+?),"
    match = re.search(quantification_pattern, theorem)

    if not match:
        return f"Variable Declaration Error: Could not find variable declarations in theorem: {theorem}"

    quantification_part = match.group(1).strip()

    # Now find all variable groups within the quantification part
    # Look for patterns like (A B : Point), (AB CD : Line), (a b c : Circle)
    var_group_pattern = r"\(([^)]+)\)"
    var_groups = re.findall(var_group_pattern, quantification_part)

    if not var_groups:
        return f"Variable Declaration Error: Could not find variable groups in quantification: {quantification_part}"

    point_names: list[str] = []
    line_names: list[str] = []
    circle_names: list[str] = []
    ordered_names: list[str] = []

    # Process groups in the order they appear to preserve original binder order
    for var_group in var_groups:
        var_group = var_group.strip()
        if ": Point" in var_group:
            # Extract point names: "A B : Point" -> ["A", "B"]
            points_str = var_group.split(": Point")[0].strip()
            names = points_str.split()
            point_names.extend(names)
            ordered_names.extend(names)
        elif ": Line" in var_group:
            # Extract line names: "AB CD : Line" -> ["AB", "CD"]
            lines_str = var_group.split(": Line")[0].strip()
            names = lines_str.split()
            line_names.extend(names)
            ordered_names.extend(names)
        elif ": Circle" in var_group:
            # Extract circle names: "a b c : Circle" -> ["a", "b", "c"]
            circles_str = var_group.split(": Circle")[0].strip()
            names = circles_str.split()
            circle_names.extend(names)
            ordered_names.extend(names)

    return point_names, line_names, circle_names, ordered_names


def parse_trace_state_output(stdout: str) -> tuple[str, str] | None:
    """Parse the trace_state output from lake env lean stdout.

    Returns:
        tuple[str, str] | None: (simplified_premises, simplified_conclusion), or None if not found
    """
    # Look for the trace_state output pattern
    # The pattern should handle any combination and order of Point, Line, Circle types
    # Examples:
    # - "a b : Circle\nP Q : Point\nh : premises ⊢ conclusion"
    # - "AB CD : Line\nh : premises ⊢ conclusion"
    # - "P Q : Point\nAB : Line\na : Circle\nh : premises ⊢ conclusion"

    # More robust pattern that matches any variable declarations followed by h: premises ⊢ conclusion
    # This handles any combination of Point, Line, Circle in any order
    robust_pattern = r"(?:.*?:\s*(?:Point|Line|Circle).*?)*h\s*:\s*(.*?)⊢\s*(.*)"
    match = re.search(robust_pattern, stdout, re.DOTALL)

    if not match:
        # Try the simple pattern as fallback - just look for h: ... ⊢ ...
        simple_pattern = r"h\s*:\s*(.*?)⊢\s*(.*)"
        simple_match = re.search(simple_pattern, stdout, re.DOTALL)
        if simple_match:
            premises = simple_match.group(1).strip()
            conclusion = simple_match.group(2).strip()
            return premises, conclusion
        return None

    # Extract both the h: part (premises) and the ⊢ part (conclusion)
    simplified_premises = match.group(1).strip()
    simplified_conclusion = match.group(2).strip()
    return simplified_premises, simplified_conclusion


def reconstruct_simplified_theorem(original_theorem: str, simplified_premises: str, simplified_conclusion: str) -> str:
    """Reconstruct the theorem string with simplified primitive relations.

    Args:
        original_theorem: The original theorem with composite relations
        simplified_premises: The simplified premises from trace_state
        simplified_conclusion: The simplified conclusion from trace_state

    Returns:
        str: The reconstructed theorem with primitive relations
    """
    # Clean up redundant indentation from the simplified premises
    premises_lines = simplified_premises.split("\n")
    cleaned_premises_lines = []
    for line in premises_lines:
        stripped = line.strip()
        if stripped:
            cleaned_premises_lines.append(stripped)
    cleaned_premises = " ".join(cleaned_premises_lines)

    # Clean up redundant indentation from the simplified conclusion
    conclusion_lines = simplified_conclusion.split("\n")
    cleaned_conclusion_lines = []
    for line in conclusion_lines:
        stripped = line.strip()
        if stripped:
            cleaned_conclusion_lines.append(stripped)
    cleaned_conclusion = " ".join(cleaned_conclusion_lines)

    # Extract quantification from original theorem (everything from ∀ to the comma)
    quantification_pattern = r"(∀.+?),"
    match = re.search(quantification_pattern, original_theorem)

    if not match:
        raise ValueError(f"Could not parse theorem quantification: {original_theorem}")

    quantification = match.group(1).strip()

    # Reconstruct with both cleaned simplified premises and conclusion
    return f"{quantification}, {cleaned_premises} → {cleaned_conclusion}"


class Simplifier:
    """Simplifier class for converting composite relations to primitive relations."""

    def __init__(self, root_dir: str, tmp_dir: str, relations_file: str) -> None:
        self.root_dir = root_dir
        self.tmp_dir = tmp_dir
        self.relations_file = relations_file
        os.makedirs(self.tmp_dir, exist_ok=True)

    def simplify(self, theorem: str, instance_name: str = "temp_simplify") -> str | tuple[None, str]:
        """Simplify a theorem by converting composite relations to primitive relations.

        Args:
            theorem: The theorem string with composite relations
            instance_name: Name for temporary files

        Returns:
            str | tuple[None, str]: The simplified theorem string, or (None, error message) if failed
        """
        try:
            # Step 1: Extract variable names
            result = extract_variables_from_theorem(theorem)
            # If the result is a string, it means there is an error in the theorem
            if isinstance(result, str):
                return None, result
            point_names, line_names, circle_names, ordered_names = result
            if len(point_names) + len(line_names) + len(circle_names) != len(ordered_names):
                return None, ("Variable Declaration Error: Binder count mismatch while reconstructing variable order.")
            # print(f"📝 Extracted points: {point_names}")
            # print(f"📝 Extracted lines: {line_names}")
            # print(f"📝 Extracted circles: {circle_names}")

            # Step 2: Create temporary Lean file
            tmp_file = os.path.join(self.tmp_dir, f"{instance_name}.lean")

            # Clean up old file if exists
            if os.path.isfile(tmp_file):
                try:
                    os.remove(tmp_file)
                    print(f"🔨 Removed old tmp file {tmp_file}")
                except OSError as e:
                    print(f"⚠️  Failed to remove old tmp file {tmp_file}: {e}")

            # Write the temporary Lean file
            lean_content = format_lean_simplifier_file(theorem, self.relations_file, ordered_names)
            with open(tmp_file, "w", encoding="utf-8") as file:
                file.write(lean_content)
                print(f"🔨 Created new file {tmp_file}")

            # Step 3: Run lake env lean to compile and capture stdout
            command = ["lake", "env", "lean", tmp_file]

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
                        print(f"❗ Simplifier Warning(s) for {tmp_file}:", end=" ")
                        print(stderr)
                        print("+" * 60)

                    if not stdout:
                        print("⚠️  No stdout output from lake build")
                        return None, "No stdout output from lake build"

                    stdout = stdout.strip()
                    # print("-" * 80)
                    # print("📝 Lake build output:")
                    # print(stdout)

                    # Step 4: Parse trace_state output
                    parse_result = parse_trace_state_output(stdout)
                    if not parse_result:
                        # Process stdout as error message
                        # Remove the file path from the error message
                        # First try the standard format with line:column
                        error = re.sub(r"/[^:]+:\d+:\d+: ", "", stdout)
                        # Then, try a more general pattern to without line:column numbers
                        error = re.sub(r"/[^\n]*?(?=(?:error|warning):\s?)", "", error, flags=re.MULTILINE)
                        error = error.strip()
                        print(f"⚠️  Could not extract simplified premises and conclusion from trace_state: {error}")
                        return None, error
                    simplified_premises, simplified_conclusion = parse_result

                    # Reconstruct the simplified theorem
                    simplified_theorem = reconstruct_simplified_theorem(theorem, simplified_premises, simplified_conclusion)

                    return simplified_theorem

            except (SubprocessError, OSError) as e:
                print(f"⚠️  Failed to execute lake build: {e}")
                return None, f"Failed to execute lake build: {e}"
            except Exception as e:
                print(f"⚠️  Unexpected error {type(e).__name__}: {e}")
                return None, f"Unexpected error {type(e).__name__}: {e}"
            finally:
                if process and process.pid:
                    kill_process_group(process.pid)

        except Exception as e:
            print(f"⚠️  Unexpected error before lake build: {type(e).__name__}: {e}")
            return None, f"Unexpected error before lake build: {type(e).__name__}: {e}"


def main() -> None:
    """Test the simplifier with example theorems."""
    # Example theorem from DSL_Parallel_Thm03.lean
    theorem_1 = (  # noqa: F841
        "∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ "
        "distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ twoLinesIntersectAtPoint UW QX V ∧ "
        "between U V W ∧ sequentiallyAlignedList [Q, S, V, X] ∧ sameSideDistinctList [R, U] QX ∧ sameSideDistinctList [T, W] QX ∧ "
        "∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT"
    )
    theorem_2 = (  # noqa: F841
        "∀ (T U V W : Point) (UV TW UT VW VT : Line), formQuadrilateral U V T W UV TW UT VW ∧ distinctPointsOnLine V T VT ∧ "
        "formTriangle U V T UV VT UT ∧ formTriangle V W T VW TW VT ∧ |(T─U)| = |(V─W)| ∧ ¬ UT.intersectsLine VW → "
        "(△ T:U:V).congruent (△ V:W:T)"
    )
    theorem_3 = (  # noqa: F841
        "∀ (G H K I J : Point) (GH HK GK HJ : Line), "
        "formTriangle G H K GH HK GK ∧ I.onLine GH ∧ "
        "between G H I ∧ H.onLine HJ ∧ J.onLine HJ ∧ ¬(J.onLine GH) ∧ "
        "¬(K.onLine GH) ∧ J.sameSide K GH ∧ ¬(GK.intersectsLine HJ) → True"
    )
    theorem_4 = (  # noqa: F841
        "∀ (Q S T R U V : Point), ∃ (QS ST QT RU UV RV : Line), "
        "formTriangle Q S T QS ST QT ∧ formTriangle R U V RU UV RV ∧ "
        "∠ U:R:V = ∠ S:T:Q ∧ |(R─V)| / |(Q─T)| = |(R─U)| / |(S─T)| → "
        "∠ R:U:V = ∠ Q:S:T"
    )

    test_list = [theorem_1, theorem_2, theorem_3, theorem_4]

    # Set up directories
    root_dir = os.path.abspath("LeanEuclidPlus")
    tmp_dir = os.path.join(
        root_dir,
        "tmp",
        "simplify",
        "test_simplifier",
    )
    os.makedirs(tmp_dir, exist_ok=True)
    print(f"🔨 Using temporary directory: {tmp_dir}")

    # Create simplifier instance
    simplifier = Simplifier(root_dir=root_dir, tmp_dir=tmp_dir, relations_file="Relations_oracle")

    print("🔬 Testing LeanEuclid Simplifier")
    print("=" * 80)

    for idx, theorem in enumerate(test_list):
        print("📝 Original theorem with composite relations:")
        print("-" * 80)
        print(theorem)
        print("=" * 80)

        # Test simplification
        print("🚀 Running simplification...")
        simplified_theorem = simplifier.simplify(theorem, f"test_{idx}")

        if isinstance(simplified_theorem, str):
            print(f"✅ Simplified theorem: {simplified_theorem}")
        else:
            assert (
                isinstance(simplified_theorem, tuple) and simplified_theorem[0] is None
            ), f"Unexpected simplified theorem, expected tuple[None, str], got {simplified_theorem}"
            print(f"❌ Simplification failed: {simplified_theorem[1]}")
        print("=" * 80)


if __name__ == "__main__":
    main()
