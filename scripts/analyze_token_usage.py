# License: Apache 2.0


# Standard Library Modules
import json
import os
import statistics
from pathlib import Path
from typing import Any, Literal, TypeAlias


# Type Aliases
UsageFormat: TypeAlias = Literal["openai", "bedrock", "openrouter"]


def normalize_usage_data(token_data: dict[str, Any], usage_format: UsageFormat) -> dict[str, Any]:
    normalized_data: dict[str, Any] = {}

    # Bedrock format (inputTokens, outputTokens)
    if usage_format == "bedrock":
        # inputTokens means non-cached input tokens
        cached_input_tokens = token_data.get("cacheReadInputTokens", 0)
        non_cached_input_tokens = token_data.get("inputTokens", 0)
        normalized_data["input_tokens"] = cached_input_tokens + non_cached_input_tokens
        normalized_data["output_tokens"] = token_data.get("outputTokens", 0)
        normalized_data["total_tokens"] = token_data.get("totalTokens", 0)

        # Handle input tokens details
        normalized_data["input_tokens_details"] = {"cached_tokens": cached_input_tokens, "non_cached_tokens": non_cached_input_tokens}

        # For Bedrock, we don't have reasoning tokens breakdown, so set to 0
        normalized_data["output_tokens_details"] = {"reasoning_tokens": 0}

    # OpenAI format (input_tokens, output_tokens)
    elif usage_format == "openai":
        normalized_data["input_tokens"] = token_data.get("input_tokens", 0)
        normalized_data["output_tokens"] = token_data.get("output_tokens", 0)
        normalized_data["total_tokens"] = token_data.get("total_tokens", 0)

        # Handle input tokens details
        input_details = token_data.get("input_tokens_details", {})
        normalized_data["input_tokens_details"] = {
            "cached_tokens": input_details.get("cached_tokens", 0),
            "non_cached_tokens": input_details.get("non_cached_tokens", 0),
        }

        # Handle output tokens details
        output_details = token_data.get("output_tokens_details", {})
        normalized_data["output_tokens_details"] = {"reasoning_tokens": output_details.get("reasoning_tokens", 0)}

    # OpenRouter format (prompt_tokens, completion_tokens, total_tokens, etc.)
    elif usage_format == "openrouter":
        # Check if it's a nested tokens schema
        normalized_data["input_tokens"] = token_data.get("prompt_tokens", 0)
        normalized_data["output_tokens"] = token_data.get("completion_tokens", 0)
        normalized_data["total_tokens"] = token_data.get("total_tokens", 0)

        # Handle input tokens details
        input_details = token_data.get("prompt_tokens_details", {})
        normalized_data["input_tokens_details"] = {
            "cached_tokens": input_details.get("cached_tokens", 0),
            "non_cached_tokens": normalized_data["input_tokens"] - input_details.get("cached_tokens", 0),
        }

        # Handle output tokens details
        output_details = token_data.get("completion_tokens_details", {})
        normalized_data["output_tokens_details"] = {"reasoning_tokens": output_details.get("reasoning_tokens", 0)}

    # Sanity check
    assert (
        normalized_data["total_tokens"] == normalized_data["input_tokens"] + normalized_data["output_tokens"]
    ), f"Total tokens mismatch: {token_data}"

    return normalized_data


def get_token_usage(file_path: str, usage_format: UsageFormat) -> dict[str, Any] | None:
    """
    Extract token usage information from a .txt file.

    Args:
        file_path (str): Path to the .txt file
        usage_format (UsageFormat): Format of the token usage data

    Returns:
        dict: Dictionary containing token usage information, or None if not found
    """
    try:
        with open(file_path, "r", encoding="utf-8") as file:
            content = file.read()

        # Find the token usage section
        start_marker = "Accumulated Token Usage:"
        end_marker = "============================================================"

        start_idx = content.find(start_marker)
        if start_idx == -1:
            return None

        # Find the end of the token usage section
        end_idx = content.find(end_marker, start_idx)
        if end_idx == -1:
            # If no end marker found, look for the next section
            sections = content.split("============================================================")
            for i, section in enumerate(sections):
                if start_marker in section:
                    if i + 1 < len(sections):
                        # Take everything up to the next section
                        token_section = section[section.find(start_marker) :]
                        break
                    # Last section, take everything after start marker
                    token_section = section[section.find(start_marker) :]
                    break
            else:
                return None
        else:
            # Extract the token usage section
            token_section = content[start_idx:end_idx]

        # Find the JSON part (between the start marker and the end)
        json_start = token_section.find("{")
        json_end = token_section.rfind("}") + 1

        if json_start == -1 or json_end == 0:
            return None

        json_str = token_section[json_start:json_end]

        # Parse the JSON
        token_data = json.loads(json_str)

        # Normalize the data to a consistent format
        return normalize_usage_data(token_data, usage_format)

    except Exception as e:
        print(f"Error parsing {file_path}: {e}")
        return None


def collect_token_data_from_directory(directory_path: str, usage_format: UsageFormat) -> list[dict[str, Any]]:
    """
    Collect token usage data from all .txt files in a directory.

    Args:
        directory_path (str): Path to the directory containing .txt files
        usage_format (UsageFormat): Format of the token usage data

    Returns:
        list[dict[str, Any]]: List of token usage data dictionaries
    """
    token_data_list = []

    # Walk through all files in the directory
    for root, _, files in os.walk(directory_path):
        for file in files:
            if file.endswith(".txt"):
                file_path = os.path.join(root, file)
                usage = get_token_usage(file_path, usage_format)
                if usage:
                    token_data_list.append(usage)

    return token_data_list


def calculate_token_costs(
    token_data: dict[str, Any], input_cost_per_million: float = 2.0, cached_input_cost_per_million: float = 0.5, output_cost_per_million: float = 8.0
) -> dict[str, float]:
    """
    Calculate costs for token usage.

    Args:
        token_data (dict[str, Any]): Token usage data
        input_cost_per_million (float): Cost per million input tokens (default: $2.0)
        cached_input_cost_per_million (float): Cost per million cached input tokens (default: $0.5)
        output_cost_per_million (float): Cost per million output tokens (default: $8.0)

    Returns:
        dict[str, float]: Dictionary with cost breakdown
    """
    input_tokens = token_data.get("input_tokens", 0)
    output_tokens = token_data.get("output_tokens", 0)
    total_tokens = token_data.get("total_tokens", 0)
    input_token_cached = token_data.get("input_tokens_details", {}).get("cached_tokens", 0)
    input_token_not_cached = input_tokens - input_token_cached

    # Calculate costs
    input_cost_not_cached = (input_token_not_cached / 1_000_000) * input_cost_per_million
    input_cost_cached = (input_token_cached / 1_000_000) * cached_input_cost_per_million
    output_cost = (output_tokens / 1_000_000) * output_cost_per_million
    total_cost = input_cost_not_cached + input_cost_cached + output_cost

    return {
        "input_cost_not_cached": input_cost_not_cached,
        "input_cost_cached": input_cost_cached,
        "input_cost": input_cost_not_cached + input_cost_cached,
        "output_cost": output_cost,
        "total_cost": total_cost,
        "input_tokens_not_cached": input_token_not_cached,
        "input_tokens_cached": input_token_cached,
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "total_tokens": total_tokens,
    }


def calculate_statistics(data_list: list[int | float]) -> dict[str, int | float]:
    """
    Calculate basic statistics for a list of numbers.

    Args:
        data_list (list[int | float]): List of numbers to analyze

    Returns:
        dict[str, int | float]: Dictionary with mean, median, min, max, total
    """
    if not data_list:
        return {"mean": 0, "median": 0, "min": 0, "max": 0, "total": 0}

    return {
        "mean": statistics.mean(data_list),
        "median": statistics.median(data_list),
        "min": min(data_list),
        "max": max(data_list),
        "total": sum(data_list),
    }


def analyze_token_usage_with_costs(
    directory_path: str,
    usage_format: UsageFormat,
    input_cost_per_million: float = 2.0,
    cached_input_cost_per_million: float = 0.5,
    output_cost_per_million: float = 8.0,
) -> dict[str, Any]:
    """
    Analyze token usage and costs across all .txt files in a directory.

    Args:
        directory_path (str): Path to the directory containing .txt files
        usage_format (UsageFormat): Format of the token usage data
        input_cost_per_million (float): Cost per million input tokens (default: $2.0)
        cached_input_cost_per_million (float): Cost per million cached input tokens (default: $0.5)
        output_cost_per_million (float): Cost per million output tokens (default: $8.0)

    Returns:
        dict: Summary statistics of token usage and costs
    """
    token_data_list = collect_token_data_from_directory(directory_path, usage_format)

    if not token_data_list:
        return {"error": "No token usage data found"}

    # Calculate token statistics
    input_tokens = [data.get("input_tokens", 0) for data in token_data_list]
    output_tokens = [data.get("output_tokens", 0) for data in token_data_list]
    total_tokens = [data.get("total_tokens", 0) for data in token_data_list]
    reasoning_tokens = [data.get("output_tokens_details", {}).get("reasoning_tokens", 0) for data in token_data_list]
    input_tokens_cached = [data.get("input_tokens_details", {}).get("cached_tokens", 0) for data in token_data_list]

    # Calculate cost statistics
    cost_data_list = [
        calculate_token_costs(data, input_cost_per_million, cached_input_cost_per_million, output_cost_per_million) for data in token_data_list
    ]

    input_costs_not_cached = [cost_data["input_cost_not_cached"] for cost_data in cost_data_list]
    input_costs_cached = [cost_data["input_cost_cached"] for cost_data in cost_data_list]
    input_costs = [cost_data["input_cost"] for cost_data in cost_data_list]
    output_costs = [cost_data["output_cost"] for cost_data in cost_data_list]
    total_costs = [cost_data["total_cost"] for cost_data in cost_data_list]

    summary = {
        "total_requests": len(token_data_list),
        "cost_settings": {
            "input_cost_per_million": input_cost_per_million,
            "cached_input_cost_per_million": cached_input_cost_per_million,
            "output_cost_per_million": output_cost_per_million,
        },
        "input_costs_not_cached": calculate_statistics(input_costs_not_cached),
        "input_costs_cached": calculate_statistics(input_costs_cached),
        "input_costs": calculate_statistics(input_costs),
        "output_costs": calculate_statistics(output_costs),
        "total_costs": calculate_statistics(total_costs),
        "input_tokens": calculate_statistics(input_tokens),
        "cached_tokens": calculate_statistics(input_tokens_cached),
        "output_tokens": calculate_statistics(output_tokens),
        "reasoning_tokens": calculate_statistics(reasoning_tokens),
        "total_tokens": calculate_statistics(total_tokens),
    }

    return summary


def print_statistics_section(stats: dict[str, int | float], title: str, is_cost: bool = False) -> None:
    """
    Print a formatted statistics section.

    Args:
        stats (dict[str, int | float]): Statistics dictionary
        title (str): Section title
        is_cost (bool): Whether this is a cost section (affects formatting)
    """
    print(f"{title}:")
    if is_cost:
        print(f"  Mean: ${stats.get('mean', 0):.4f}")
        print(f"  Median: ${stats.get('median', 0):.4f}")
        print(f"  Min: ${stats.get('min', 0):.4f}")
        print(f"  Max: ${stats.get('max', 0):.4f}")
        print(f"  Total: ${stats.get('total', 0):.4f}")
    else:
        print(f"  Mean: {stats.get('mean', 0):.1f}")
        print(f"  Median: {stats.get('median', 0):.1f}")
        print(f"  Min: {stats.get('min', 0)}")
        print(f"  Max: {stats.get('max', 0)}")
        print(f"  Total: {stats.get('total', 0):,}")
    print()


def print_token_analysis_with_costs(analysis: dict[str, Any], title: str = "Token Usage Analysis") -> None:
    """
    Print a formatted token usage analysis with cost information.

    Args:
        analysis (dict): Analysis results from analyze_token_usage_with_costs
        title (str): Title for the analysis
    """
    if "error" in analysis:
        print(f"{title}: {analysis['error']}")
        return

    print(f"\n{title}")
    print("=" * 60)
    print(f"Total requests analyzed: {analysis.get('total_requests', 0)}")

    # Print cost settings
    cost_settings = analysis.get("cost_settings", {})
    print(f"Input Price Not Cached: ${cost_settings.get('input_cost_per_million', 0):.2f}/million tokens")
    print(f"Input Price Cached: ${cost_settings.get('cached_input_cost_per_million', 0):.2f}/million tokens")
    print(f"Output Price: ${cost_settings.get('output_cost_per_million', 0):.2f}/million tokens")
    print()

    # Print cost statistics
    print_statistics_section(analysis.get("input_costs_not_cached", {}), "Input Costs Not Cached ($)", is_cost=True)
    print_statistics_section(analysis.get("input_costs_cached", {}), "Input Costs Cached ($)", is_cost=True)
    print_statistics_section(analysis.get("input_costs", {}), "Input Costs ($)", is_cost=True)
    print_statistics_section(analysis.get("output_costs", {}), "Output Costs ($)", is_cost=True)
    print_statistics_section(analysis.get("total_costs", {}), "Total Costs ($)", is_cost=True)

    # Print token statistics
    print_statistics_section(analysis.get("input_tokens", {}), "Input Tokens")
    print_statistics_section(analysis.get("cached_tokens", {}), "Cached Tokens")
    print_statistics_section(analysis.get("output_tokens", {}), "Output Tokens")
    print_statistics_section(analysis.get("reasoning_tokens", {}), "Reasoning Tokens")
    print_statistics_section(analysis.get("total_tokens", {}), "Total Tokens")

    print("=" * 60)


def analyze_multiple_directories(root_dir: str, directory_configs: list[tuple[str, UsageFormat, float, float, float]]) -> dict[str, dict[str, Any]]:
    """
    Analyze token usage and costs for multiple directories with different cost configurations.

    Args:
        root_dir (str): Root directory path
        directory_configs (list[tuple[str, UsageFormat, float, float, float]]): List of 5-tuples containing:
            - subdir (str): Subdirectory path relative to root_dir
            - usage_format (UsageFormat): Format of the token usage data
            - input_cost_per_million (float): Cost per million input tokens
            - cached_input_cost_per_million (float): Cost per million cached input tokens
            - output_cost_per_million (float): Cost per million output tokens

    Returns:
        dict[str, dict[str, Any]]: Dictionary mapping subdirectory names to analysis results
    """
    results = {}

    for subdir, usage_format, input_cost, cached_input_cost, output_cost in directory_configs:
        full_dir_path = os.path.join(root_dir, subdir)
        analysis = analyze_token_usage_with_costs(
            full_dir_path,
            usage_format,
            input_cost_per_million=input_cost,
            cached_input_cost_per_million=cached_input_cost,
            output_cost_per_million=output_cost,
        )
        results[subdir] = analysis

    return results


def main() -> None:
    # Build absolute root_dir from repository root to avoid CWD issues
    scripts_dir = Path(__file__).resolve().parent
    repo_root = scripts_dir.parent
    result_dir_name = "result_dsl-learned_p0"
    root_dir = str(repo_root / "LeanEuclidPlus" / result_dir_name / "response")

    directory_configs: list[tuple[str, UsageFormat, float, float, float]] = [
        ("UniGeo/text-only/4_formalized-structure/gpt-5-2025-08-07_medium/1-shot_Similarity-1", "openai", 1.25, 0.125, 10.0),
        ("UniGeo/text-only/4_formalized-structure/qwen/qwen3-235b-a22b-2507/1-shot_Similarity-1", "openrouter", 0.13, 0.13, 0.6),
        ("UniGeo/text-only/4_formalized-structure/anthropic/claude-sonnet-4-thinking/1-shot_Similarity-1", "openrouter", 3.0, 0.3, 15.0),
    ]

    analyses = analyze_multiple_directories(root_dir, directory_configs)

    # Save the analysis to JSON files
    os.makedirs("token_analysis", exist_ok=True)
    for subdir, analysis in analyses.items():
        file_name = f"{result_dir_name}/{subdir}"
        file_path = f"token_analysis/{file_name.replace('/', '_')}.json"
        with open(file_path, "w", encoding="utf-8") as f:
            json.dump(analysis, f, indent=4)

    # Print the analyses
    for subdir, analysis in analyses.items():
        model_name = subdir.split("/")[-2]  # Extract model name from path
        print_token_analysis_with_costs(analysis, f"{model_name} Model Token Usage")


if __name__ == "__main__":
    main()
