# License: Apache 2.0


# Standard Library Modules
import argparse
import re
from pathlib import Path

# External Modules
import pandas as pd
from openpyxl.styles import Alignment

# Constants
METHOD_ORDER = ["1_direct", "2_self-refine_compile", "3_semi-formalize", "4_formalized-structure"]
MODEL_ORDER = ["gpt-4.1-nano-2025-04-14", "gpt-4.1-mini-2025-04-14", "gpt-4.1-2025-04-14", "o4-mini-2025-04-16", "o3-2025-04-16"]


def parse_overall_summary(file_path: str) -> dict | None:
    """Parse overall_summary.txt file to extract metrics."""
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()
        # Extract rates using regex
        compilation_rate_match = re.search(r"Total Compilation Rate: ([\d.]+)", content)
        equivalent_rate_match = re.search(r"Total Equivalent Rate: ([\d.]+)", content)
        likely_equivalent_rate_match = re.search(r"Total Likely Equivalent Rate: ([\d.]+)", content)
        if not (compilation_rate_match and equivalent_rate_match and likely_equivalent_rate_match):
            return None
        compilation_rate = float(compilation_rate_match.group(1))
        equivalent_rate = float(equivalent_rate_match.group(1))
        likely_equivalent_rate = float(likely_equivalent_rate_match.group(1))
        return {"compilation_rate": compilation_rate, "equivalent_rate": equivalent_rate, "likely_equivalent_rate": likely_equivalent_rate}
    except Exception as e:
        print(f"Error parsing {file_path}: {e}")
        return None


def format_cell_value(metrics: dict | None, missing: bool = False) -> str:
    """Format metrics into the required cell format: 'compilation, sum=(equivalent+likely)'."""
    if missing:
        return "0, 0=(0+0)"
    if metrics is None:
        return ""
    compilation_pct = int(metrics["compilation_rate"] * 100)
    equivalent_pct = int(metrics["equivalent_rate"] * 100)
    likely_equivalent_pct = int(metrics["likely_equivalent_rate"] * 100)
    sum_pct = equivalent_pct + likely_equivalent_pct
    return f"{compilation_pct}, {sum_pct}=({equivalent_pct}+{likely_equivalent_pct})"


def get_pipeline_description(method: str) -> str:
    """Get pipeline description based on method."""
    method_descriptions = {
        "1_direct": "Step 1: Informal Statement -> Formal Statement",
        "2_self-refine_compile": "Step 1: Informal Statement -> Formal Statement\nStep 2: Self-Refine for Compilation Errors (1 Retry)",
        "3_semi-formalize": (
            "Step 1: Informal Statement -> Semi-Formalized Structure\n"
            "Step 2: Semi-Formalized Structure -> Formalized Statement\n"
            "Step 3: Self-Refine for Compilation Errors (1 Retry)"
        ),
        "4_formalized-structure": (
            "Step 1: Informal Statement -> Semi-Formalized Structure\n"
            "Step 2: Semi-Formalized Structure -> Formalized Structure\n"
            "Step 3: Formalized Structure -> Formal Statement\n"
            "Step 4: Self-Refine for Compilation Errors (1 Retry)"
        ),
    }
    return method_descriptions.get(method, method)


def format_excel_with_wrapping(df: pd.DataFrame, sheet_name: str, writer: pd.ExcelWriter) -> None:
    """Write DataFrame to Excel with text wrapping for Pipeline column."""
    df.to_excel(writer, sheet_name=sheet_name, index=False)
    worksheet = writer.sheets[sheet_name]

    # Set text wrapping for Pipeline column (column A)
    for row in range(2, len(df) + 2):  # Start from row 2 (after header)
        cell = worksheet[f"A{row}"]
        cell.alignment = Alignment(wrap_text=True, vertical="top")

    # Auto-adjust column widths
    worksheet.column_dimensions["A"].width = 50  # Pipeline column wider
    for col in range(2, len(df.columns) + 1):  # Other columns
        col_letter = chr(64 + col)  # B, C, D, etc.
        worksheet.column_dimensions[col_letter].width = 20


def _traverse_directory_structure(mode_path: Path) -> tuple[dict[str, set[str]], set[str]]:
    """Traverse directory structure and collect method shots and models."""
    shot_collector: dict[str, set[str]] = {method: set() for method in METHOD_ORDER}
    model_collector: set[str] = set()

    for method_dir in mode_path.iterdir():
        if not method_dir.is_dir() or method_dir.name not in METHOD_ORDER:
            continue
        method = method_dir.name
        for model_dir in method_dir.iterdir():
            if not model_dir.is_dir():
                continue
            model_collector.add(model_dir.name)
            for shot_dir in model_dir.iterdir():
                if shot_dir.is_dir():
                    shot_collector[method].add(shot_dir.name)

    return shot_collector, model_collector


def _collect_methods_and_models(mode_path: Path) -> tuple[dict[str, list[str]], list[str]]:
    """Collect shot types for each method and all models from directory structure."""
    shot_collector, model_collector = _traverse_directory_structure(mode_path)

    # Sort shot types for each method
    method_shots: dict[str, list[str]] = {}
    for method in METHOD_ORDER:
        method_shots[method] = sorted(shot_collector[method], key=lambda x: (int(x.split("-")[0]), x))

    # Use fixed MODEL_ORDER, but only include models that exist in the directory
    available_models = [model for model in MODEL_ORDER if model in model_collector]

    return method_shots, available_models


def _collect_results_data(mode_path: Path, method_shots: dict[str, list[str]]) -> dict[tuple[str, str], dict[str, tuple[dict | None, bool]]]:
    """Collect results data from directory structure."""
    results: dict[tuple[str, str], dict[str, tuple[dict | None, bool]]] = {}

    for method_dir in mode_path.iterdir():
        if not method_dir.is_dir() or method_dir.name not in METHOD_ORDER:
            continue
        method = method_dir.name
        for model_dir in method_dir.iterdir():
            if not model_dir.is_dir():
                continue
            model = model_dir.name
            for shot_dir in model_dir.iterdir():
                if not shot_dir.is_dir() or shot_dir.name not in method_shots[method]:
                    continue
                shot_type = shot_dir.name
                summary_file = shot_dir / "overall_summary.txt"
                missing = not summary_file.exists()
                metrics = parse_overall_summary(str(summary_file)) if not missing else None
                key = (method, shot_type)
                if key not in results:
                    results[key] = {}
                results[key][model] = (metrics, missing)

    return results


def _build_result_rows(
    method_shots: dict[str, list[str]],
    expected_models: list[str],
    results: dict[tuple[str, str], dict[str, tuple[dict | None, bool]]],
) -> list[dict]:
    """Build result rows for DataFrame."""
    rows = []
    for method in METHOD_ORDER:
        pipeline_desc = get_pipeline_description(method)
        for shot in method_shots[method]:
            row = {"Pipeline": pipeline_desc, "Examples": shot}
            for model in expected_models:
                metrics, missing = results.get((method, shot), {}).get(model, (None, True))
                row[model] = format_cell_value(metrics, missing)
            rows.append(row)
    return rows


def _validate_paths(result_dir: str, benchmark: str, mode: str) -> Path | None:
    """Validate that result paths exist and return mode_path if valid, None otherwise."""
    benchmark_path = Path(result_dir) / benchmark
    if not benchmark_path.exists():
        print(f"Benchmark path {benchmark_path} does not exist!")
        return None
    mode_path = benchmark_path / mode
    if not mode_path.exists():
        print(f"Mode path {mode_path} does not exist!")
        return None
    return mode_path


def analyze_results(result_dir: str, benchmark: str, mode: str = "text-only") -> pd.DataFrame:
    """Analyze results and return DataFrame with 'Examples' column and model columns."""
    mode_path = _validate_paths(result_dir, benchmark, mode)
    if mode_path is None:
        return pd.DataFrame()

    # Collect methods, shots, and models
    method_shots, expected_models = _collect_methods_and_models(mode_path)

    # Collect results data
    results = _collect_results_data(mode_path, method_shots)

    # Build result rows
    rows = _build_result_rows(method_shots, expected_models, results)

    df = pd.DataFrame(rows)
    # Reorder columns
    df = df[["Pipeline", "Examples"] + expected_models]
    return df


def _write_excel_and_preview(dataframes: dict[str, pd.DataFrame], output_file: str) -> None:
    """Write dataframes to Excel file with formatting and print previews."""
    with pd.ExcelWriter(output_file, engine="openpyxl") as writer:
        for sheet_name, df in dataframes.items():
            format_excel_with_wrapping(df, sheet_name, writer)

    print(f"Results saved to {output_file}")
    for sheet_name, df in dataframes.items():
        print(f"\nPreview ({sheet_name}):")
        print(df.to_string(index=False, max_colwidth=50))


def write_unigeo_combined_excel(result_dir: str, benchmark: str, output_file: str) -> None:
    """Write both text-only and multi-modal results to a single Excel file with two sheets for UniGeo."""
    df_text = analyze_results(result_dir, benchmark, "text-only")
    df_multi = analyze_results(result_dir, benchmark, "multi-modal")

    dataframes = {"text-only": df_text, "multi-modal": df_multi}
    _write_excel_and_preview(dataframes, output_file)


def main() -> None:
    parser = argparse.ArgumentParser(description="Analyze experiment results and create Excel table")
    parser.add_argument(
        "--result_dir",
        type=str,
        default="../LeanEuclidPlus/result/equivalence",
        help="Result directory (default: LeanEuclidPlus/result/equivalence)",
    )
    parser.add_argument("--benchmark", type=str, default="UniGeo", help="Benchmark name (UniGeo, Book, etc.)")
    parser.add_argument("--mode", type=str, default="text-only", help="Mode to analyze (text-only, multi-modal)")
    parser.add_argument("--output_file", type=str, default="UniGeo_results.xlsx", help="Output file (default: UniGeo_results.xlsx)")

    args = parser.parse_args()

    if args.benchmark == "UniGeo":
        write_unigeo_combined_excel(args.result_dir, args.benchmark, args.output_file)
    else:
        raise ValueError(f"Unsupported benchmark: {args.benchmark}")


if __name__ == "__main__":
    main()
