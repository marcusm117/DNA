# License: Apache 2.0
# Code Adapted from: https://github.com/loganrjmurphy/LeanEuclid/blob/master/AutoFormalization/statement/evaluate.py


# Standard Library Modules
import argparse
import json
import os
import re

# External Modules
from joblib import Parallel, delayed

# Internal Modules
from path import ROOT_DIR
from dna.leaneuclid import EquivalenceChecker

# from dna.leaneuclid_simplifier import Simplifier
from dna import (
    OPENAI_O_MODEL_LIST,
    OPENAI_GPT5_MODEL_LIST,
    OPENROUTER_GPT_OSS_MODEL_LIST,
)


# Constants
# Set a time limit that balances completeness and efficiency
BIN_TIME = 120
# Set of OpenAI models that support reasoning effort
OPENAI_REASONING_MODEL_SET = set(OPENAI_O_MODEL_LIST + OPENAI_GPT5_MODEL_LIST + OPENROUTER_GPT_OSS_MODEL_LIST)


# Set Environment Variables
# Each checker will spawn 2 subprocesses for z3 and cvc5
os.environ["OMP_NUM_THREADS"] = "2"


def build_example_choices_str(num_examples: int, example_choices: list[str]) -> str:
    """Build the example choices suffix used in result directory names.

    The format must match the directory names created elsewhere:
    - 0 example:   "0-shot"
    - 1 example:   "1-shot_<choice>"
    - N examples:  "N-shot_<choice1+choice2+...>"
    """
    if num_examples == 0:
        return "0-shot"
    if num_examples == 1:
        return "1-shot_" + example_choices[0]
    flattened_example_choices = "+".join(example_choices)
    return str(num_examples) + "-shot_" + flattened_example_choices


def calculate_summary_statistics(summary_list: list[dict]) -> tuple[dict[str, int], dict[str, float]]:
    """Calculate summary statistics from a list of summary dictionaries"""
    # Calculate counts
    total_count = sum(summary["total_count"] for summary in summary_list)
    validated_count = sum(summary["validated_count"] for summary in summary_list)
    validation_error_count = sum(summary["validation_error_count"] for summary in summary_list)
    equiv_count = sum(summary["equiv_count"] for summary in summary_list)
    likely_equiv_count = sum(summary["likely_equiv_count"] for summary in summary_list)
    not_equiv_count = sum(summary["not_equiv_count"] for summary in summary_list)
    no_conclusion_count = sum(summary["no_conclusion_count"] for summary in summary_list)
    checking_error_count = sum(summary["checking_error_count"] for summary in summary_list)

    # Calculate rates
    validation_rate = validated_count / total_count
    equiv_rate = equiv_count / total_count
    likely_equiv_rate = likely_equiv_count / total_count
    not_equiv_rate = not_equiv_count / total_count
    no_conclusion_rate = no_conclusion_count / total_count
    error_rate = checking_error_count / total_count

    count_stats = {
        "total_count": total_count,
        "validated_count": validated_count,
        "validation_error_count": validation_error_count,
        "equiv_count": equiv_count,
        "likely_equiv_count": likely_equiv_count,
        "not_equiv_count": not_equiv_count,
        "no_conclusion_count": no_conclusion_count,
        "checking_error_count": checking_error_count,
    }
    rate_stats = {
        "validation_rate": validation_rate,
        "equiv_rate": equiv_rate,
        "likely_equiv_rate": likely_equiv_rate,
        "not_equiv_rate": not_equiv_rate,
        "no_conclusion_rate": no_conclusion_rate,
        "error_rate": error_rate,
    }

    return count_stats, rate_stats


def write_summary_file(
    summary_file: str,
    count_stats: dict[str, int],
    rate_stats: dict[str, float],
    args: argparse.Namespace,
    category: str = "",
    run_idx: int = 0,
    prefix: str = "",
) -> None:
    """Write summary statistics to a file with consistent formatting"""
    with open(summary_file, "w", encoding="utf-8") as f:
        f.write("===================================================================\n")
        f.write(f"Setting: {args}\n")
        if category:
            f.write(f"Category: {category}\n")
        if run_idx:
            f.write(f"Run: {run_idx}\n")
        f.write(f"{prefix} Total Count: {count_stats['total_count']}\n")
        f.write("===================================================================\n")
        f.write(f"{prefix} Validated Count: {count_stats['validated_count']}\n")
        f.write(f"{prefix} Validation Rate: {rate_stats['validation_rate']:.4f}\n")
        f.write("===================================================================\n")
        f.write(f"{prefix} Validation Error Count: {count_stats['total_count'] - count_stats['validated_count']}\n")
        f.write(f"{prefix} Equivalent Count: {count_stats['equiv_count']}\n")
        f.write(f"{prefix} Likely Equivalent Count: {count_stats['likely_equiv_count']}\n")
        f.write(f"{prefix} Not Equivalent Count: {count_stats['not_equiv_count']}\n")
        f.write(f"{prefix} No Conclusion Count: {count_stats['no_conclusion_count']}\n")
        f.write(f"{prefix} Checking Error Count: {count_stats['checking_error_count']}\n")
        f.write("===================================================================\n")
        f.write(f"{prefix} Equivalent Rate: {rate_stats['equiv_rate']:.4f}\n")
        f.write(f"{prefix} Likely Equivalent Rate: {rate_stats['likely_equiv_rate']:.4f}\n")
        f.write(f"{prefix} Not Equivalent Rate: {rate_stats['not_equiv_rate']:.4f}\n")
        f.write(f"{prefix} No Conclusion Rate: {rate_stats['no_conclusion_rate']:.4f}\n")
        f.write(f"{prefix} Checking Error Rate: {rate_stats['error_rate']:.4f}\n")
        f.write("===================================================================\n")


def print_summary_to_console(count_stats: dict[str, int], rate_stats: dict[str, float], prefix: str = "Overall") -> None:
    """Print summary statistics to console with consistent formatting"""
    print("=" * 80)
    print(f"🎯 {prefix} EVALUATION SUMMARY")
    print("=" * 80)
    print(f"{prefix} Count: {count_stats['total_count']}")
    print(f"{prefix} Validated Count: {count_stats['validated_count']}")
    print(f"{prefix} Validation Rate: {rate_stats['validation_rate']:.4f}")
    print("-" * 80)
    print(f"{prefix} Validation Error Count: {count_stats['total_count'] - count_stats['validated_count']}")
    print(f"{prefix} Equivalent Count: {count_stats['equiv_count']}")
    print(f"{prefix} Likely Equivalent Count: {count_stats['likely_equiv_count']}")
    print(f"{prefix} Not Equivalent Count: {count_stats['not_equiv_count']}")
    print(f"{prefix} No Conclusion Count: {count_stats['no_conclusion_count']}")
    print(f"{prefix} Checking Error Count: {count_stats['checking_error_count']}")
    print("-" * 80)
    print(f"{prefix} Equivalent Rate: {rate_stats['equiv_rate']:.4f}")
    print(f"{prefix} Likely Equivalent Rate: {rate_stats['likely_equiv_rate']:.4f}")
    print(f"{prefix} Not Equivalent Rate: {rate_stats['not_equiv_rate']:.4f}")
    print(f"{prefix} No Conclusion Rate: {rate_stats['no_conclusion_rate']:.4f}")
    print(f"{prefix} Checking Error Rate: {rate_stats['error_rate']:.4f}")
    print("=" * 80)


def create_run_summary(category: str, run_idx: int, result_dir_base: str, run_result_list: list[str], args: argparse.Namespace) -> dict[str, int]:
    # Create a summary file for this run
    run_summary_dir = os.path.join(result_dir_base, category, f"run_{run_idx}")
    run_summary_file = os.path.join(run_summary_dir, "run_summary.txt")

    # Calculate the result distribution
    # We first calculate the validation rate, which is the number of files
    # in the pred_dir divided by the total number of problems (testing_idx) of this run
    total_count_run = len(args.testing_idx)
    validated_count = len(os.listdir(run_summary_dir.replace("equivalence", "statement")))
    validation_error_count = sum(1 for res in run_result_list if res == "validation_error")

    # Check if the validation error count is correct
    assert validated_count + validation_error_count == total_count_run, "The validation error count does not match the total count"

    # We then calculate the rate of "equiv", "likely_equiv", "no_conclusion", "not_equiv", and "checking_error"
    equiv_count = sum(1 for res in run_result_list if res == "equiv")
    likely_equiv_count = sum(1 for res in run_result_list if res == "likely_equiv")
    not_equiv_count = sum(1 for res in run_result_list if res == "not_equiv")
    no_conclusion_count = sum(1 for res in run_result_list if res == "no_conclusion")
    checking_error_count = sum(1 for res in run_result_list if res == "checking_error")

    # Check if the sum of checked counts matches the total validated count
    assert (
        equiv_count + likely_equiv_count + not_equiv_count + no_conclusion_count + checking_error_count == validated_count
    ), "The sum of counts does not match the total validated count"

    count_stats = {
        "total_count": total_count_run,
        "validated_count": validated_count,
        "validation_error_count": validation_error_count,
        "equiv_count": equiv_count,
        "likely_equiv_count": likely_equiv_count,
        "not_equiv_count": not_equiv_count,
        "no_conclusion_count": no_conclusion_count,
        "checking_error_count": checking_error_count,
    }
    rate_stats = {
        "validation_rate": validated_count / total_count_run,
        "equiv_rate": equiv_count / total_count_run,
        "likely_equiv_rate": likely_equiv_count / total_count_run,
        "not_equiv_rate": not_equiv_count / total_count_run,
        "no_conclusion_rate": no_conclusion_count / total_count_run,
        "error_rate": checking_error_count / total_count_run,
    }

    # Save the run summary
    write_summary_file(run_summary_file, count_stats, rate_stats, args, category=category, run_idx=run_idx, prefix=f"{category} Run-{run_idx}")

    print(f"✅ Run {run_idx} evaluation completed!")
    return count_stats


def create_category_summary(
    category: str, result_dir_base: str, category_result_dict: dict[int, list[str]], args: argparse.Namespace
) -> dict[str, int]:
    # Create a summary file for this category
    category_summary_dir = os.path.join(result_dir_base, category)
    category_summary_file = os.path.join(category_summary_dir, "category_summary.txt")

    # Fetch the summary for each run
    run_summary_dict: dict[int, dict[str, int]] = {}
    for run_idx, run_result_list in category_result_dict.items():
        run_summary = create_run_summary(category, run_idx, result_dir_base, run_result_list, args)
        run_summary_dict[run_idx] = run_summary

    # Calculate summary statistics using the helper function
    count_stats, rate_stats = calculate_summary_statistics(list(run_summary_dict.values()))

    # Save the category summary file
    write_summary_file(category_summary_file, count_stats, rate_stats, args, category=category, prefix=category)

    # Print category summary to console
    print_summary_to_console(count_stats, rate_stats, prefix=category)

    print(f"✅ Category {category} evaluation completed!")
    return count_stats


def create_overall_summary(args: argparse.Namespace, category_summary_list: list[dict]) -> None:
    """Create overall summary from individual category summaries"""
    # Reconstruct the example choices string exactly as used for directory creation
    example_choices_str = build_example_choices_str(args.num_examples, args.example_choices)

    # Create the overall summary file path consistent with result directory structure
    model_dir_name = f"{args.model}_{args.openai_reasoning_effort}" if args.model in OPENAI_REASONING_MODEL_SET else args.model
    overall_summary_file = os.path.join(
        args.root_dir,
        args.result_dir_name,
        "equivalence",
        args.dataset,
        args.reasoning,
        args.method,
        model_dir_name,
        example_choices_str,
        "overall_summary.txt",
    )

    # Ensure the parent directory exists (defensive, should already exist)
    os.makedirs(os.path.dirname(overall_summary_file), exist_ok=True)

    # Calculate summary statistics using the helper function
    count_stats, rate_stats = calculate_summary_statistics(category_summary_list)

    # Write the overall summary file
    write_summary_file(overall_summary_file, count_stats, rate_stats, args, prefix="Overall")

    # Print overall summary to console
    print_summary_to_console(count_stats, rate_stats, prefix="Overall")
    print("🎉 All categories evaluated successfully!")
    print(f"📁 Overall summary saved to: {overall_summary_file}")
    print("=" * 80)


def evaluate_single_instance(
    category: str,
    run_idx: int,
    instance_idx: int,
    pred_file: str,
    checker: EquivalenceChecker,
    args: argparse.Namespace,
) -> tuple[str, str, int]:
    """Process a single evaluation instance synchronously for multiprocessing"""
    if os.path.exists(pred_file):
        # get the prediction file, only contains prediction for now
        with open(pred_file, "r", encoding="utf-8") as f:
            data = json.load(f)

        # get the ground truth from the formalization file
        file_name = f"Prop{instance_idx:02d}.lean" if args.dataset == "Book" else f"Thm{instance_idx:02d}.lean"
        # note that args.category is a list of categories, but we are only checking one category at a time!
        formalization_path = os.path.join(args.root_dir, args.dataset, category, "formalizations", file_name)
        with open(formalization_path, "r", encoding="utf-8") as f:
            formalization = f.read()
            pattern = r"theorem\s?\w+\s?:\s?(.*?)\s?\:\="
            match = re.search(pattern, formalization, re.DOTALL)
            if match:
                formalized_statement = match.group(1)
                formalized_statement = re.sub(r"\s+", " ", formalized_statement)
            else:
                raise ValueError(f"⚠️  Could not extract formalized statement from {formalization_path}")

        # will add ground truth to the prediction file later
        pred = data["prediction"]
        gt = formalized_statement

        print("+" * 100)
        print(f"Testing {instance_idx}th problem in category {category} and run {run_idx}: {pred_file}")
        final_result: str
        final_result, checker_result, full_result = checker.check(gt, pred, str(instance_idx))

        # Store the ground_truth, final_result, checker_result & full_result, to the pred_file for better visualization and debugging
        data["ground_truth"] = formalized_statement
        data["final_result"] = final_result
        data["checker_result"] = checker_result
        data["full_result"] = full_result
        with open(pred_file, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=4, ensure_ascii=False)
        print(f"🔨 Added ground_truth, final_result, checker_result & full_result to {pred_file}")
        print("+" * 100)
        return final_result, category, run_idx

    print(f"⚠️  Prediction file not found: {pred_file}")
    return "validation_error", category, run_idx


def evaluate_all_categories(args: argparse.Namespace, checker_args: dict) -> list[dict]:
    """Process evaluation for all categories"""
    print("Categories: ", args.category)
    # Construct directory name for in-context examples setting
    example_choices_str = build_example_choices_str(args.num_examples, args.example_choices)

    # Create base directories for all categories
    model_dir_name = f"{args.model}_{args.openai_reasoning_effort}" if args.model in OPENAI_REASONING_MODEL_SET else args.model

    pred_dir_base = os.path.join(
        args.root_dir,
        args.result_dir_name,
        "statement",
        args.dataset,
        args.reasoning,
        args.method,
        model_dir_name,
        example_choices_str,
    )
    tmp_dir_base = os.path.join(
        args.root_dir,
        "tmp",
        "check",
        args.result_dir_name,
        args.dataset,
        args.reasoning,
        args.method,
        model_dir_name,
        example_choices_str,
    )
    result_dir_base = os.path.join(
        args.root_dir,
        args.result_dir_name,
        "equivalence",
        args.dataset,
        args.reasoning,
        args.method,
        model_dir_name,
        example_choices_str,
    )

    # Create base directories
    print(f"📂 Creating tmp directory: {tmp_dir_base}")
    os.makedirs(tmp_dir_base, exist_ok=True)
    print(f"📂 Creating result directory: {result_dir_base}")
    os.makedirs(result_dir_base, exist_ok=True)

    # Create tasks for all instances across all categories
    task_list: list[tuple[str, int, int, str, EquivalenceChecker, argparse.Namespace]] = []
    for category in args.category:
        for run_idx in range(1, args.num_run + 1):
            # Create directories for this category-run combination
            pred_dir = os.path.join(pred_dir_base, category, f"run_{run_idx}")
            tmp_dir = os.path.join(tmp_dir_base, category, f"run_{run_idx}")
            result_dir = os.path.join(result_dir_base, category, f"run_{run_idx}")
            # Create a checker instance for this category-run combination
            checker = EquivalenceChecker(
                root_dir=args.root_dir,
                tmp_dir=tmp_dir,
                result_dir=result_dir,
                ground_relations_file=args.ground_relations_file,
                test_relations_file=args.test_relations_file,
                mode=checker_args["mode"],
                # Always simplify the ground truth and model prediction to make it easier for the SMT solver
                skip_simp=False,
                n_perms=checker_args["n_perms"],
                bin_time=checker_args["bin_time"],
                approx_time=checker_args["approx_time"],
            )
            # Create tasks for each instance in this category-run combination
            for instance_idx in args.testing_idx:
                pred_file = os.path.join(pred_dir, str(instance_idx) + ".json")
                task_list.append((category, run_idx, instance_idx, pred_file, checker, args))

    # Execute all tasks with multiprocessing and progress bar
    print(f"🚀 Starting joblib evaluation of {len(task_list)} instances with max {args.num_process} workers...")

    # Use joblib with enhanced built-in progress tracking
    result_list = Parallel(
        n_jobs=args.num_process,
        verbose=10,  # More detailed progress (0=quiet, 10=very verbose, 50=debug)
        backend="loky",  # Use loky backend for cross-platform robustness
        batch_size=int(args.batch_size),  # Default is "auto"
        max_nbytes=None,  # No memory limit
        pre_dispatch="2*n_jobs",  # Pre-dispatch tasks for better performance
    )(
        delayed(evaluate_single_instance)(category, run_idx, instance_idx, pred_file, checker, args)
        for category, run_idx, instance_idx, pred_file, checker, args in task_list
    )

    # Classify the results by category and by runs
    result_dict: dict[str, dict[int, list[str]]] = {}
    for result, category, run_idx in result_list:
        if category not in result_dict:
            result_dict[category] = {}
        if run_idx not in result_dict[category]:
            result_dict[category][run_idx] = []
        result_dict[category][run_idx].append(result)

    # Save a summary file for each category and each run
    category_summary_list: list[dict] = []
    for category, category_result_dict in result_dict.items():
        category_summary = create_category_summary(category, result_dir_base, category_result_dict, args)
        category_summary_list.append(category_summary)

    return category_summary_list


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--dataset",
        type=str,
        choices=["Book", "UniGeo"],
        required=True,
        help="Testing dataset",
    )
    parser.add_argument(
        "--category",
        type=str,
        nargs="+",
        choices=[
            "",
            "Parallel",
            "Triangle",
            "Quadrilateral",
            "Congruent",
            "Similarity",
            "Additional",
        ],
        required=True,
        help="Testing category",
    )
    parser.add_argument(
        "--method",
        type=str,
        choices=["1_direct", "2_self-refine", "3_semi-formalize", "4_formalized-structure", "5_implicit-inference", "6_self-refine_semantic"],
        required=True,
        help="Method to use for autoformalization",
    )
    parser.add_argument(
        "--model",
        type=str,
        required=True,
        help="Model to use for autoformalization",
    )
    parser.add_argument(
        "--openai_reasoning_effort",
        type=str,
        choices=["minimal", "low", "medium", "high"],
        default="medium",
        help="Reasoning effort",
    )
    parser.add_argument(
        "--mode",
        choices=["bvars", "skipApprox", "onlyApprox", "full", "precheck", "naive", "separate", "precheck+separate"],
        default="precheck+separate",
        help="E3 checker mode",
    )
    parser.add_argument(
        "--reasoning",
        type=str,
        choices=["text-only", "multi-modal"],
        required=True,
        help="Reasoning Type",
    )
    parser.add_argument("--num_examples", type=int, default=0, help="Number of examples")
    parser.add_argument("--example_choices", type=str, nargs="+", default=["none"], help="Choices of in-context examples")
    parser.add_argument("--num_process", type=int, default=100, help="Maximum number of parallel processes")
    parser.add_argument("--batch_size", default="auto", help="Number of tasks assigned to each parallel process at a time")
    parser.add_argument("--num_run", type=int, default=5, help="Number of runs for sampling")
    parser.add_argument("--root_dir", type=str, default=ROOT_DIR, help="Root directory")
    parser.add_argument("--result_dir_name", type=str, default="result", help="Name of the result directory")
    parser.add_argument(
        "--ground_relations_file",
        type=str,
        default="Relations",
        help="Name of the UniGeo-specific relations file under the directory, for simplification of the ground truth",
    )
    parser.add_argument(
        "--test_relations_file",
        type=str,
        default="Relations_barebone",
        help="Name of the UniGeo-specific relations file under the directory, for simplification of the model prediction",
    )

    args = parser.parse_args()

    # Add additional arguments
    if args.dataset == "UniGeo":
        # The category for UniGeo can either be "Additional" or combination of other categories
        if args.category == ["Additional"]:
            args.testing_idx = list(range(1, 41))
        # "Additional" can't be mixed with other categories
        elif "Additional" not in args.category:
            args.testing_idx = list(range(1, 21))
        else:
            raise ValueError(f"Invalid category: {args.category}")
    else:  # Book / Euclid"s Elements
        args.testing_idx = [i for i in range(1, 49) if i not in [2, 6, 12, 32, 42]]

    print("------------------------------------------------------------")
    print(f"🔧 Set OMP_NUM_THREADS to {os.environ['OMP_NUM_THREADS']}")
    print("args: ", args)
    print("------------------------------------------------------------")

    # Prepare checker arguments for multiprocessing
    checker_args = {
        "mode": args.mode,
        "n_perms": 3,
        "bin_time": BIN_TIME,
        "approx_time": 5,
    }

    # Process each category and collect summaries
    category_summary_list = evaluate_all_categories(args, checker_args)

    # Create overall summary
    create_overall_summary(args, category_summary_list)


if __name__ == "__main__":
    main()
