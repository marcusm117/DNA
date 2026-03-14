# License: Apache 2.0


# Standard Library Modules
import os
import re

# External Modules
from joblib import Parallel, delayed

# Internal Modules
from dna.leaneuclid import EquivalenceChecker


# Constants
BIN_TIME = 15
PLACEHOLDER_STATEMENT = "∀ (A B : Point) (AB : Line), distinctPointsOnLine A B AB → A ≠ B"


def extract_theorem_statement(file_path: str) -> str:
    """Extract the theorem statement from a Lean file"""
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    # Find the theorem statement using regex
    pattern = r"theorem\s+\w+\s*:\s*(.*?)\s*:="
    match = re.search(pattern, content, re.DOTALL)

    if match:
        statement = match.group(1).strip()
        # Clean up whitespace
        statement = re.sub(r"\s+", " ", statement)
        return statement

    raise ValueError(f"Could not extract theorem statement from {file_path}")


def validate_single_ground_truth(
    category: str,
    theorem_file: str,
    checker: EquivalenceChecker,
    _base_dir: str,
) -> tuple[str, str, str]:
    """Validate a single ground truth statement using naive mode"""
    # Extract the ground truth statement
    ground_truth = extract_theorem_statement(theorem_file)

    # Get theorem name for logging
    theorem_name = theorem_file.split("/")[-1].replace(".lean", "")

    print(f"🔍 Testing {theorem_name} in category {category}")

    # Check equivalence (should be UNSAT for valid ground truth)
    _, checker_result, _ = checker.check(PLACEHOLDER_STATEMENT, ground_truth, theorem_name)

    if checker_result is False:
        return "checking_error", category, theorem_name

    # If no checking error, return the `ground_result`
    assert isinstance(checker_result, tuple)
    return checker_result[0], category, theorem_name


def get_all_theorem_files(base_dir: str) -> list[tuple[str, str]]:
    """Get all theorem files from all UniGeo categories"""
    categories = [
        "Additional",
        # "Parallel",
        # "Triangle",
        # "Quadrilateral",
        # "Congruent",
        # "Similarity",
    ]
    theorem_files = []

    for category in categories:
        formalization_dir = os.path.join(base_dir, "UniGeo", category, "formalizations")
        if os.path.exists(formalization_dir):
            for file in os.listdir(formalization_dir):
                if file.endswith(".lean"):
                    file_path = os.path.join(formalization_dir, file)
                    theorem_files.append((category, file_path))

    return theorem_files


def main() -> None:
    # Set up paths
    base_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), "../LeanEuclidPlus"))
    # tmp_dir = os.path.join(os.path.dirname(__file__), "ground_truth_validation", "tmp")
    # result_dir = os.path.join(os.path.dirname(__file__), "ground_truth_validation", "result")
    tmp_dir = os.path.join(os.path.dirname(__file__), "ground_truth_validation")
    result_dir = os.path.join(os.path.dirname(__file__), "ground_truth_validation")

    # Create base directories
    os.makedirs(tmp_dir, exist_ok=True)
    os.makedirs(result_dir, exist_ok=True)

    # Get all theorem files
    theorem_files = get_all_theorem_files(base_dir)

    def extract_instance_index(file_path: str) -> int:
        """Return the numeric instance index like 01 from a path ending with Thm01.lean."""
        match = re.search(r"Thm(\d+)", os.path.basename(file_path))
        if match is None:
            raise ValueError(f"Unexpected theorem filename: {file_path}")
        return int(match.group(1))

    # Sort theorem files by instance idx like `Thm01.lean`, `Thm02.lean`, etc.
    theorem_files.sort(key=lambda x: extract_instance_index(x[1]))

    print(f"📊 Found {len(theorem_files)} theorem files to validate")
    print("=" * 80)

    # Create tasks for parallel processing
    task_list = []
    for category, theorem_file in theorem_files:
        # Create category-specific directories
        category_tmp_dir = os.path.join(tmp_dir, category)
        category_result_dir = os.path.join(result_dir, category)
        os.makedirs(category_tmp_dir, exist_ok=True)
        os.makedirs(category_result_dir, exist_ok=True)

        # Create category-specific checker instance. Use the absolute repo path
        # for `root_dir` so that joblib workers launched by Loky resolve the
        # Lean project correctly even when their working directory differs from
        # the parent process.
        category_checker = EquivalenceChecker(
            root_dir=base_dir,
            mode="naive",
            bin_time=BIN_TIME,
            tmp_dir=category_tmp_dir,
            result_dir=category_result_dir,
            ground_relations_file="Relations",
            test_relations_file="Relations",
        )

        task_list.append((category, theorem_file, category_checker, base_dir))

    # Execute validation with multiprocessing
    print(f"🚀 Starting validation of {len(task_list)} theorems with 100 workers...")

    result_list = Parallel(
        n_jobs=100,
        verbose=10,
        backend="loky",
        batch_size="auto",
        max_nbytes=None,
        pre_dispatch="2*n_jobs",
    )(delayed(validate_single_ground_truth)(category, theorem_file, checker, base_dir) for category, theorem_file, checker, base_dir in task_list)

    # Analyze results
    print("\n" + "=" * 80)
    print("📊 VALIDATION RESULTS SUMMARY")
    print("=" * 80)

    total_count = len(result_list)
    valid_count = sum(1 for result, _, _ in result_list if result == "VALID")
    timeout_count = sum(1 for result, _, _ in result_list if result == "TIMEOUT")
    unknown_count = sum(1 for result, _, _ in result_list if result == "UNKNOWN")
    unsat_count = sum(1 for result, _, _ in result_list if result == "UNSAT")
    precheck_error_count = sum(1 for result, _, _ in result_list if result.startswith("pre-check_failed"))
    other_error_count = sum(1 for result, _, _ in result_list if result == "checking_error")
    assert (
        valid_count + timeout_count + unknown_count + unsat_count + precheck_error_count + other_error_count == total_count
    ), "Total count does not match!"

    print(f"🔢 Total theorems: {total_count}")
    print(f"✅ VALID: {valid_count}")
    print(f"❓ TIMEOUT: {timeout_count}")
    print(f"⚠️  UNKNOWN: {unknown_count}")
    print(f"❌ UNSAT: {unsat_count}")
    print(f"❌ PRE-CHECK ERROR: {precheck_error_count}")
    print(f"❌ OTHER ERROR: {other_error_count}")

    # Print problematic theorems
    print("=" * 80)
    print("🚨 PROBLEMATIC GROUND TRUTH THEOREMS")
    print("=" * 80)

    problematic_found = False
    for result, category, theorem_name in result_list:
        if result in {"UNSAT", "checking_error", "UNKNOWN"} or result.startswith("pre-check_failed"):
            problematic_found = True
            print(f"❌ {category}/{theorem_name}: {result}")

    if not problematic_found:
        print("🎉 All ground truth statements are either VALID or TIMEOUT!")

    print("=" * 80)


if __name__ == "__main__":
    main()
