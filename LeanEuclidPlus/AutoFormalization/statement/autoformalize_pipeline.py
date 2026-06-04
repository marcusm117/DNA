# License: Apache 2.0
# pylint: disable=R0903,R0912,R0916,R0801,R1714,W0603,C0302


# Standard Library Modules
import argparse
import asyncio
import json
import os
import random
import re
import shutil
from typing import Any, Awaitable

# External Modules
import json5
from joblib import Parallel, delayed
from tqdm.asyncio import tqdm

# Internal Modules
from path import (
    EXAMPLE_DIR,
    ROOT_DIR,
)
from dna import (
    create_unified_model,
    UnifiedModel,
    OPENAI_GPT_MODEL_LIST,
    OPENAI_O_MODEL_LIST,
    OPENAI_GPT5_MODEL_LIST,
    BEDROCK_CLAUDE_MODEL_LIST,
    BEDROCK_CLAUDE_THINKING_MODEL_LIST,
    OPENROUTER_CLAUDE_MODEL_LIST,
    OPENROUTER_CLAUDE_THINKING_MODEL_LIST,
    OPENROUTER_QWEN3_MODEL_LIST,
    OPENROUTER_QWEN3_THINKING_MODEL_LIST,
    OPENROUTER_GEMMA3_MODEL_LIST,
    OPENROUTER_GPT_OSS_MODEL_LIST,
    OPENROUTER_DEEPSEEK_MODEL_LIST,
    OPENROUTER_DEEPSEEK_THINKING_MODEL_LIST,
    lean_error,
    parse_error,
)
from dna.type_defs import Content, Messages
from dna.leaneuclid import Validator


# Fix random seed
random.seed(42)


# Constants
REASONING_MODEL_SET = set[str](OPENAI_O_MODEL_LIST + OPENAI_GPT5_MODEL_LIST + BEDROCK_CLAUDE_THINKING_MODEL_LIST + OPENROUTER_GPT_OSS_MODEL_LIST)
LOCAL_VLLM_MODEL_LIST = [
    "FrenzyMath/Herald_translator",
    "AI-MO/Kimina-Autoformalizer-7B",
    "huawei-ai4math/Mathesis-Autoformalizer",
    "huawei-ai4math/Mathesis-Autoformalizer-HPO",
]
LOCAL_VLLM_MODEL_NEW_LIST = [
    "stepfun-ai/StepFun-Formalizer-7B",
    "stepfun-ai/StepFun-Formalizer-32B",
    "Goedel-LM/Goedel-Formalizer-V2-8B",
    "Goedel-LM/Goedel-Formalizer-V2-32B",
]


# Lazy-loaded example pool cache
_example_pool_cache: dict[str, str] | None = None


def validate_unigeo_alias(alias: str) -> bool:
    pattern = r"^[A-Z][a-z]+-\d$"
    if not re.match(pattern, alias):
        return False
    category, example_idx = alias.split("-")
    if category not in ["Parallel", "Triangle", "Quadrilateral", "Congruent", "Similarity"]:
        return False
    if example_idx not in ["1", "2", "3", "4", "5"]:
        return False
    return True


def construct_instruction(args: argparse.Namespace) -> Content:
    # Construct the instruction head based on the dataset and reasoning type
    if args.dataset == "UniGeo":
        if args.reasoning == "multi-modal":
            instruction_head = (
                "You are given a diagram and an English Statement of a theorem from Euclidean Geometry. "
                "Note that all points and lines mentioned in the statement are distinct, unless otherwise implied by some premises.\n\n"
            )
        else:
            instruction_head = (
                "You are given an English Statement of a theorem from Euclidean Geometry. "
                "Note that all points and lines mentioned in the statement are distinct, unless otherwise implied by some premises.\n\n"
            )
    else:
        raise NotImplementedError("Currently, only UniGeo dataset is supported for autoformalization.")

    # Load the instruction based on the method
    instruction = ""
    pipeline_prompt = (
        "Your task is to formalize the English Statement into a formal statement in Lean 4 "
        "strictly adhering to the following formal definitions and guidelines.\n\n"
    )
    # Load the documentations for the SystemE DSL
    with open(f"instructions/{args.dsl_doc}", "r", encoding="utf-8") as f:
        dsl_doc = f.read()

    if args.method == "1_direct":
        with open("instructions/1_direct.txt", "r", encoding="utf-8") as f:
            instruction = instruction_head + pipeline_prompt + dsl_doc + "\n\n" + f.read()
    elif args.method == "2_self-refine":
        with open("instructions/2_self-refine.txt", "r", encoding="utf-8") as f:
            instruction = instruction_head + pipeline_prompt + dsl_doc + "\n\n" + f.read()
    elif args.method == "3_semi-formalize":
        pipeline_prompt = (
            "Your task is to first semi-formalize the English Statement into a json-style structure "
            "(see Guidelines #2), and then convert the Semi-Formalized Structure into a formal statement in Lean 4 "
            "strictly adhering to the following formal definitions and guidelines.\n\n"
        )
        with open("instructions/3_semi-formalize.txt", "r", encoding="utf-8") as f:
            instruction = instruction_head + pipeline_prompt + dsl_doc + "\n\n" + f.read()
    elif args.method == "4_formalized-structure":
        pipeline_prompt = (
            "Your task is to first semi-formalize the English Statement into a json-style structure "
            "(see Guidelines #2), then formalize each clause in the Semi-Formalized Structure "
            "resulting in a Formalized Structure (see Guidelines #3), "
            "and finally convert the Formalized Structure into a formal statement in Lean 4 "
            "strictly adhering to the following formal definitions and guidelines.\n\n"
        )
        with open("instructions/4_formalized-structure.txt", "r", encoding="utf-8") as f:
            instruction = instruction_head + pipeline_prompt + dsl_doc + "\n\n" + f.read()
    else:
        raise ValueError(f"Invalid method: {args.method}")

    # Append the instruction to the instruction content
    instruction_content = [{"type": "input_text", "text": instruction}]

    return instruction_content


def get_example_pool() -> dict[str, str]:
    """Lazy-load the example pool only when dynamic examples are needed."""
    global _example_pool_cache
    if _example_pool_cache is None:
        _example_pool_cache = {}
        # Define the example choices to load
        example_aliases = [
            "Parallel-1",
            "Triangle-1",
            "Quadrilateral-1",
            "Congruent-1",
            "Similarity-1",
            "Parallel-3",
        ]

        # Load problem text from files for each example choice
        for alias in example_aliases:
            category, example_idx = alias.split("-")
            # Load clean text for UniGeo dataset (following the pattern used elsewhere)
            clean_text_path = os.path.join(EXAMPLE_DIR, "UniGeo", category, "clean_texts", f"{example_idx}.txt")
            with open(clean_text_path, "r", encoding="utf-8") as f:
                _example_pool_cache[alias] = f.read().strip()

    return _example_pool_cache


async def select_dynamic_examples(
    category: str,
    instance_idx: int,
    problem_text: str,
    num_examples: int,
    example_pool: dict[str, str],
    llm: UnifiedModel,
    client: Any,
    args: argparse.Namespace,
    num_attempt: int = 3,
) -> list[str]:
    # Format the example pool as pretty JSON for the LLM
    example_pool_pretty = json.dumps(example_pool, indent=4, ensure_ascii=False)
    example_alias_str = ", ".join(example_pool.keys())
    # Prompt for selecting dynamic examples
    prompt = (
        "You are given an English statement of a theorem from Euclidean Geometry:"
        f"\n\n{problem_text}\n\n"
        "Your task is to select the most relevant examples from a pool of human expert formalization examples. "
        f"You need to first choose exactly {num_examples} example(s) that will serve as your in-context examples "
        "when formalizing the given problem statement into Lean 4.\n\n"
        "## Example Pool\n"
        "Below is the example pool in JSON format with the example alias as the key and the English problem statement as the value:"
        f"\n\n{example_pool_pretty}\n\n"
        "## Selection Criteria\n"
        f"Select the top {num_examples} example(s) based on:\n\n"
        "1. **Mathematical Similarity**: Example with the most similar mathematical objects, relations, concepts, or relationships\n"
        "2. **Logical Similarity**: Example with the most similar logical structure\n"
        "3. **You Judgement**: Examples that you think are the most helpful for you to formalize the given problem statement\n\n"
        "You should think carefully step by step, compare each example in the pool with the given problem statement, "
        f"compare them against each other following the criteria above, "
        f"and finally rank and select the top {num_examples} examples based on overall relevance.\n\n"
        "## Output Format\n"
        f"Return exactly {num_examples} example alias(es) separated by commas within triple angle brackets, "
        "you should order them by relevance in descending order:\n\n"
        "<<< alias1, alias2, ... >>>"
    )
    # Message to the LLM
    messages: Messages = [{"role": "user", "content": [{"type": "input_text", "text": prompt}]}]

    for _ in range(num_attempt):
        # Get response from model
        response_text, _, _, _ = await llm.get_response_async(client, messages)

        # Add the assistant response to the context
        messages.append({"role": "assistant", "content": [{"type": "output_text", "text": response_text}]})

        # CHECK 1: The response must be surrounded by triple angle brackets
        pattern = r"<<<(.*?)>>>"
        matches = re.findall(pattern, response_text, re.DOTALL)
        if not matches:
            feedback = (
                "I couldn't find your example selection in the expected format. "
                "Please make sure to provide your selection within **triple angle brackets**: <<< alias1, alias2, ... >>>"
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            continue

        # CHECK 2: The response must be a comma-separated list of aliases in the format "Category-Number"
        model_prediction = matches[-1].strip()
        pattern = r"^[A-Z][a-z]+-\d(\s*,\s*[A-Z][a-z]+-\d)*$"
        if not re.match(pattern, model_prediction):
            feedback = (
                f"Invalid example choice format '{model_prediction}'. "
                "Each example should be in format 'Category-Number' (e.g., 'Triangle-1'). Please provide your selection again."
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            continue

        # CHECK 3: Each alias must be in the example pool
        example_choices = []
        invalid_alias = None
        for alias in model_prediction.split(","):
            alias = alias.strip()
            # Validate that alias is in the example pool
            if alias not in example_pool:
                invalid_alias = alias
                break
            example_choices.append(alias)

        if invalid_alias:
            feedback = (
                f"Invalid example choice '{invalid_alias}'. "
                f"You can only choose from the example pool:\n\n{example_alias_str}\n\n"
                "Please provide your selection again."
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            continue

        # CHECK 4: The response must contain exactly num_examples examples
        if len(example_choices) != num_examples:
            feedback = (
                f"You should select exactly {num_examples} examples, but you selected {len(example_choices)}. "
                f"Please select exactly {num_examples} example(s) again."
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            continue

        # Success - return the valid example choices
        return example_choices

    # Failed after all attempts, save the conversation history for debugging
    # Construct directory name for in-context examples setting
    log_dir = os.path.join(
        args.root_dir,
        args.result_dir_name,
        "errors",
        args.dataset,
        args.reasoning,
        args.method,
        args.model,
        f"{args.num_examples}-shot_dynamic",
    )
    os.makedirs(log_dir, exist_ok=True)

    with open(os.path.join(log_dir, f"{category}_{instance_idx}_select_dynamic_examples_failed.json"), "w", encoding="utf-8") as f:
        json.dump(messages, f, indent=4, ensure_ascii=False)

    raise ValueError(f"Failed to select dynamic examples after {num_attempt} attempts")


def construct_example_messages(
    dataset: str, num_examples: int, example_choices: list[str], args: argparse.Namespace, add_header: bool
) -> tuple[Content, Messages]:
    # We provide 2 formats for in-context examples construction:
    # 1. Content: all in-context examples are provided in a single user message content object
    # 2. Messages: each in-context example is provided in a pair of user and assistant messages,
    # where the user message contains the input text and image, and the assistant message contains the output text
    if add_header:
        example_header = "Here are some examples:\n\n" if num_examples > 1 else "Here is an example:\n\n"
        example_content: Content = [{"type": "input_text", "text": example_header}]
        example_messages: Messages = [{"role": "user", "content": [{"type": "input_text", "text": example_header}]}]
    else:
        example_content = []
        example_messages = [{"role": "user", "content": []}]

    # Parse the example choices
    example_choices_parsed: list[tuple[str, str]] = []
    for choice in example_choices:
        category, example_idx = choice.split("-")
        example_choices_parsed.append((category, example_idx))

    # Construct the in-context examples
    for category, example_idx in example_choices_parsed:
        # Load the input English Statement
        input_text = ""
        if dataset == "UniGeo":
            print("✅ In-Context Examples: Loading clean text")
            clean_text_path = os.path.join(EXAMPLE_DIR, dataset, category, "clean_texts", f"{example_idx}.txt")
            with open(clean_text_path, "r", encoding="utf-8") as f:
                input_text += f.read()
        else:
            text_path = os.path.join(EXAMPLE_DIR, dataset, category, "texts", f"{example_idx}.txt")
            with open(text_path, "r", encoding="utf-8") as f:
                input_text += f.read()

        # If reasoning is multi-modal, load the input image
        if args.reasoning == "multi-modal":
            image_path = os.path.join(EXAMPLE_DIR, dataset, category, "diagrams", f"{example_idx}.png")
            example_content.append(
                {
                    "type": "input_image",
                    "image_path": image_path,
                    "image_format": "png",
                }
            )
            example_messages[0]["content"].append({"type": "input_image", "image_path": image_path, "image_format": "png"})

        # Load formalized text from the correct directory based on the relations file
        if args.relations_file == "Relations":
            dir_suffix = ""
        elif args.relations_file == "Relations_barebone":
            dir_suffix = "_barebone"
        elif args.relations_file == "Relations_oracle":
            dir_suffix = "_oracle"
        elif args.relations_file == "Relations_learned":
            dir_suffix = "_learned"
        else:
            raise ValueError(f"Invalid relations file: {args.relations_file}")

        # Load the output Formal statement
        formalized_statement_path = os.path.join(
            EXAMPLE_DIR,
            dataset,
            category,
            f"formalizations{dir_suffix}",
            f"Example0{example_idx}.lean",
        )
        with open(formalized_statement_path, "r", encoding="utf-8") as f:
            formalized_statement = f.read()
            pattern = r"theorem\s?\w+\s?:\s?(.*?)\s?\:\="
            match = re.search(pattern, formalized_statement, re.DOTALL)
            assert match is not None, f"Formalized statement for {example_idx} not found!"
            formalized_statement = match.group(1)
            formalized_statement = re.sub(r"\s+", " ", formalized_statement)

        # Load other intermediate reasoning outputs
        semiformalized_structure = ""
        formalized_structure = ""
        declaration = ""
        formalized_text = ""

        # If pipeline has at least 3 stages, load semi-formalized structure
        if int(args.method[0]) >= 3:
            semiformalized_structure_path = os.path.join(
                EXAMPLE_DIR,
                dataset,
                category,
                "semiformalized_structures",
                f"{example_idx}.json5",
            )
            with open(semiformalized_structure_path, "r", encoding="utf-8") as f:
                # For reasoning models, load semiformalized structure without CoT in the comments
                if args.model in REASONING_MODEL_SET and (args.cot_for_reasoning_models == "no" or args.cot_for_reasoning_models == "minimal"):
                    flattened_semiformalized_structure = json5.loads(f.read().strip())
                    semiformalized_structure = json.dumps(flattened_semiformalized_structure, indent=4, ensure_ascii=False)
                else:
                    semiformalized_structure = f.read().strip()

        # If pipeline is Semi-Formalized Structure -> Formalized Statement
        # load from "formalized_texts_from_semi"
        if args.method == "3_semi-formalize":
            formalized_text_path = os.path.join(
                EXAMPLE_DIR,
                dataset,
                category,
                f"formalized_texts_from_semi{dir_suffix}",
                f"{example_idx}.txt",
            )
            with open(formalized_text_path, "r", encoding="utf-8") as f:
                # For reasoning models, load formalized text without CoT
                if args.model in REASONING_MODEL_SET and args.cot_for_reasoning_models == "no":
                    formalized_text = f.read().strip()
                    # Only keep the 3rd last line and the last line
                    formalized_text = formalized_text.split("\n")[-3] + "\n\n" + formalized_text.split("\n")[-1]
                else:
                    formalized_text = f.read().strip()

        # If pipeline is Semi-Formalized Structure -> Formalized Structure -> Formalized Statement
        # load from "formalized_structure", "declarations_from_formal" and "formalized_texts_from_formal"
        if args.method == "4_formalized-structure":
            formalized_structure_path = os.path.join(
                EXAMPLE_DIR,
                dataset,
                category,
                f"formalized_structures{dir_suffix}",
                f"{example_idx}.json5",
            )
            with open(formalized_structure_path, "r", encoding="utf-8") as f:
                # For reasoning models, load formalized structure without CoT in the comments,
                # and remove the comments
                if args.model in REASONING_MODEL_SET and (args.cot_for_reasoning_models == "no" or args.cot_for_reasoning_models == "minimal"):
                    flattened_formalized_structure = json5.loads(f.read().strip())
                    formalized_structure = json.dumps(flattened_formalized_structure, indent=4, ensure_ascii=False)
                else:
                    formalized_structure = f.read().strip()

            declaration_path = os.path.join(
                EXAMPLE_DIR,
                dataset,
                category,
                f"declarations_from_formal{dir_suffix}",
                f"{example_idx}.txt",
            )
            with open(declaration_path, "r", encoding="utf-8") as f:
                # For reasoning models, load declaration without CoT
                if args.model in REASONING_MODEL_SET and args.cot_for_reasoning_models == "no":
                    declaration = f.read().strip()
                    # Only keep the first and last lines of the declaration
                    declaration = declaration.split("\n")[0] + "\n\n" + declaration.split("\n")[-1]
                else:
                    declaration = f.read().strip()

            formalized_text_path = os.path.join(
                EXAMPLE_DIR,
                dataset,
                category,
                f"formalized_texts_from_formal{dir_suffix}",
                f"{example_idx}.txt",
            )
            with open(formalized_text_path, "r", encoding="utf-8") as f:
                # For reasoning models, load formalized text without CoT
                if args.model in REASONING_MODEL_SET and args.cot_for_reasoning_models == "no":
                    formalized_text = f.read().strip()
                    # Only keep the 3rd last line and the last line
                    formalized_text = formalized_text.split("\n")[-3] + "\n\n" + formalized_text.split("\n")[-1]
                else:
                    formalized_text = f.read().strip()

        # Construct the in-context examples
        user_input = f"English Statement:\n\n{input_text}"
        # Construct user input for the "messages" format, which is shared across all pipelines
        example_messages[0]["content"].append({"type": "input_text", "text": user_input})

        # 1-Stage & 2-Stage Naive Pipeline
        if args.method == "1_direct" or args.method == "2_self-refine":
            assistant_output = f"Formalized Statement:\n\n<<< {formalized_statement} >>>\n\n"
            # Construct input-output for the "content" format
            example_content.append(
                {
                    "type": "input_text",
                    "text": f"{user_input}\n\n\n{assistant_output}",
                }
            )
            # Construct assistant output for the "messages" format
            example_messages.append({"role": "assistant", "content": [{"type": "output_text", "text": assistant_output}]})
        # 3-Stage Decomposition Pipeline
        elif args.method == "3_semi-formalize":
            assert semiformalized_structure != "", "Semi-formalized structure should not be empty!"
            assistant_output = f"Semi-Formalized Structure:\n\n{semiformalized_structure}\n\n\n" + f"Formalized Statement:\n\n{formalized_text}\n\n"
            # Construct input-output for the "content" format
            example_content.append(
                {
                    "type": "input_text",
                    "text": f"{user_input}\n\n\n{assistant_output}",
                }
            )
            # Construct assistant output for the "messages" format
            example_messages.append({"role": "assistant", "content": [{"type": "output_text", "text": assistant_output}]})
        # 4-Stage Decomposition Pipeline
        elif args.method == "4_formalized-structure":
            assert formalized_structure != "", "Formalized structure should not be empty!"
            assistant_output = (
                f"Semi-Formalized Structure:\n\n{semiformalized_structure}\n\n\n"
                f"Formalized Structure:\n\n{formalized_structure}\n\n\n"
                f"Formalized Statement:\n\n{declaration}\n\n{formalized_text}\n\n"
            )
            # Construct input-output for the "content" format
            example_content.append(
                {
                    "type": "input_text",
                    "text": f"{user_input}\n\n\n{assistant_output}",
                }
            )
            # Construct assistant output for the "messages" format
            example_messages.append({"role": "assistant", "content": [{"type": "output_text", "text": assistant_output}]})

    return example_content, example_messages


async def process_with_semaphore(task: Awaitable[bool], semaphore: asyncio.Semaphore) -> bool:
    async with semaphore:
        return await task


def merge_usage_dicts(accumulated: dict[str, Any], new_usage: dict[str, Any]) -> dict[str, Any]:
    """Recursively merge usage dictionaries, adding numeric values and merging nested dicts."""

    for key, value in new_usage.items():
        if key not in accumulated:
            accumulated[key] = value
        elif value is None:
            # If new value is None, keep the existing value
            pass  # No change to accumulated[key]
        elif accumulated[key] is None:
            # If existing value is None and new value is not None, use the new value
            accumulated[key] = value
        elif isinstance(value, (int, float)) and isinstance(accumulated[key], (int, float)):
            # Both are numeric (int or float), add them
            accumulated[key] += value
        elif isinstance(value, dict) and isinstance(accumulated[key], dict):
            # Both are dictionaries, recursively merge
            accumulated[key] = merge_usage_dicts(accumulated[key], value)
        else:
            # Different types or other cases, raise an error
            raise ValueError(f"Invalid usage, key: {key}, value: {value}")

    return accumulated


def extract_response_text_from_file(response_file: str) -> str | None:
    """Extract the raw model `response_text` from a saved response .txt file.

    Used by --reuse_responses to recover the LLM output without re-calling the model.
    The .txt is written in autoformalize_single_instance as:
        ...\n============(60)\nModel Response Text:\n\n{response_text}\n\n============(60)\nConversation History:\n\n...
    We anchor on the surrounding labels rather than splitting on the `=` rule, because
    `response_text` itself can contain a line of 60 `=`. Returns None on any miss so the
    caller falls back to a normal LLM call (reuse-or-call semantics).
    """
    try:
        with open(response_file, "r", encoding="utf-8") as f:
            content = f.read()
    except OSError:
        return None

    start_marker = "Model Response Text:\n\n"
    end_marker = "\n" + ("=" * 60) + "\nConversation History:\n\n"
    start = content.find(start_marker)
    if start == -1:
        return None
    start += len(start_marker)
    end = content.find(end_marker, start)
    if end == -1:
        return None
    return content[start:end]


# Fields in the saved `Arguments:` record that must match the current run for a
# reused response to be a faithful sample. Plumbing/parallelism fields are excluded
# because they cannot affect the model output or the validation verdict.
REUSE_FINGERPRINT_FIELDS = (
    "dataset",
    "model",
    "method",
    "reasoning",
    "num_examples",
    "example_choices",
    "example_format",
    "temperature",
    "openai_reasoning_effort",
    "cot_for_reasoning_models",
)


def check_reuse_fingerprint(response_file: str, args: argparse.Namespace) -> None:
    """Raise if a saved response was produced under a different (faithfulness-critical) config.

    The .txt stores `Arguments:\\n\\n{str(args)}\\n\\n` (a Namespace repr). We parse the
    faithfulness-critical fields out of that repr and compare against the current run.
    A mismatch means reusing the file would silently mix incompatible samples, so we fail loudly.
    """
    try:
        with open(response_file, "r", encoding="utf-8") as f:
            content = f.read()
    except OSError:
        return

    marker = "Arguments:\n\n"
    start = content.find(marker)
    if start == -1:
        return  # no recorded args; cannot check, allow (older files)
    start += len(marker)
    end = content.find("\n\n", start)
    saved_args_repr = content[start:end] if end != -1 else content[start:]

    for field in REUSE_FINGERPRINT_FIELDS:
        current = getattr(args, field, None)
        # Match the field as it appears in the Namespace repr, e.g. model='...', temperature=0.2
        m = re.search(rf"\b{re.escape(field)}=([^,)]+)", saved_args_repr)
        if m is None:
            continue
        saved_raw = m.group(1).strip()
        if saved_raw != repr(current) and saved_raw != str(current):
            raise ValueError(
                f"--reuse_responses config mismatch in {response_file}: "
                f"field '{field}' saved={saved_raw} but current={current!r}. "
                f"Refusing to reuse responses generated under a different config."
            )


async def autoformalize_single_instance(
    category: str,
    run_idx: int,
    instance_idx: int,
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    pred_dir: str,
    response_dir: str,
    validator: Validator,
    llm: UnifiedModel,
    client: Any,
    args: argparse.Namespace,
) -> bool:
    """Process a single instance asynchronously"""

    print("------------------------------------------------------------")
    print(f"Processing instance {instance_idx} in category {category} and run {run_idx} with: {llm.model_id}")
    print(f"Inference Args: {llm.get_config()}")
    print("------------------------------------------------------------")

    # Load the problem text for user input
    problem_text = ""
    if args.dataset == "UniGeo":
        print("✅ Test: Loading clean text")
        clean_text_path = os.path.join(args.root_dir, args.dataset, category, "clean_texts", f"{instance_idx}.txt")
        with open(clean_text_path, "r", encoding="utf-8") as f:
            problem_text += f.read()
    else:
        text_path = os.path.join(args.root_dir, args.dataset, category, "texts", f"{instance_idx}.txt")
        with open(text_path, "r", encoding="utf-8") as f:
            problem_text += f.read()

    # Construct user input for the test instance
    user_content = [{"type": "input_text", "text": "Here is your problem:\n\n"}]
    if args.reasoning == "multi-modal":
        image_path = os.path.join(args.root_dir, args.dataset, category, "diagrams", f"{instance_idx}.png")
        user_content.append(
            {
                "type": "input_image",
                "image_path": image_path,
                "image_format": "png",
            }
        )
    user_content.append(
        {
            "type": "input_text",
            "text": (
                f"English Statement:\n\n{problem_text}\n\n\n"
                "Now please formalize the English Statement strictly adhering to the guidelines and examples provided above.\n\n"
            ),
        }
    )

    # Construct messages
    messages: Messages = []
    messages.append({"role": "developer", "content": system_content})

    # Only add the example messages if `num_examples` > 0
    example_choices_dynamic: list[str] = []

    # If num_examples is 0, we just add the user input as a new message
    if args.num_examples == 0:
        messages.append({"role": "user", "content": user_content})
    else:
        # If the example messages are a string, it means we are using dynamic examples
        if args.example_choices[0] == "dynamic":
            assert len(example_messages) == 0, "No static examples should be passed in when you set example_choices to 'dynamic'!"

            # Dynamically select the best examples from the example pool
            # We can do majority voting for the example choices, to reduce randomness
            example_choices_dynamic = await select_dynamic_examples(
                category, instance_idx, problem_text, args.num_examples, get_example_pool(), llm, client, args, num_attempt=3
            )
            # Construct the dynamic example messages
            example_content_dynamic, example_messages_dynamic = construct_example_messages(
                args.dataset, args.num_examples, example_choices_dynamic, args, True
            )
            # Choose the example format
            if args.example_format == "content":
                example_messages_dynamic = [{"role": "user", "content": example_content_dynamic + user_content}]
            # Add the dynamic examples to the messages
            messages.extend(example_messages_dynamic)

        # Otherwise, we are use static examples passed in
        else:
            # Choose the example format
            if args.example_format == "content":
                example_messages = [{"role": "user", "content": example_content + user_content}]
            # Add the static examples to the messages
            messages.extend(example_messages)

    # # DEBUG
    # from pprint import pprint
    # pprint(messages)

    # If method is direct, then there's no need to self-refine, so we set num_query to 1
    num_query = args.num_query
    if args.method == "1_direct" and args.num_query > 1:
        print(f"⚠️  Method is direct, setting num_query from {args.num_query} to 1!")
        num_query = 1

    # --reuse_responses is only sound for single-query methods: the saved .txt is
    # overwritten each query and retains only the final response, so multi-query
    # methods (2_self-refine, 4_formalized-structure) cannot be faithfully resumed.
    if getattr(args, "reuse_responses", False) and num_query > 1:
        raise ValueError(
            f"--reuse_responses is only supported for single-query methods (num_query == 1), "
            f"but method '{args.method}' resolved to num_query == {num_query}. "
            f"Saved responses only retain the final query and cannot faithfully reconstruct a multi-query run."
        )

    # Save the accumulated token usage from all queries
    usage_list: list[dict[str, Any]] = []
    accumulated_usage: dict[str, Any] = {}

    response_file = os.path.join(response_dir, f"{instance_idx}.txt")

    for _ in range(num_query):
        # Reuse a previously-saved response if requested and available (reuse-or-call).
        # On a hit we skip the LLM call AND skip rewriting the .txt, preserving the
        # original response + token-usage record byte-for-byte.
        reused = False
        if getattr(args, "reuse_responses", False) and os.path.exists(response_file):
            check_reuse_fingerprint(response_file, args)
            cached_text = extract_response_text_from_file(response_file)
            if cached_text is not None:
                response_text = cached_text
                reused = True
                print(f"♻️  Instance {instance_idx}: reusing saved response (no LLM call)")

        if not reused:
            # Message format will be converted internally in the UnifiedModel
            response_text, usage, reasoning_summary_list, _ = await llm.get_response_async(client, messages)

            # Save the token usage
            usage_list.append(usage)
            # Accumulate the token usage
            accumulated_usage = merge_usage_dicts(accumulated_usage, usage)

            # Save the response to a file
            os.makedirs(response_dir, exist_ok=True)
            with open(response_file, "w", encoding="utf-8") as f:
                f.write("=" * 60 + "\n")
                # save all the arguments
                f.write(f"Arguments:\n\n{str(args)}\n\n")
                f.write("=" * 60 + "\n")
                # save the English statement
                f.write(f"English Statement:\n\n{problem_text}\n\n")
                f.write("=" * 60 + "\n")
                # save the dynamic example choices, if any
                if example_choices_dynamic:
                    f.write(f"Dynamic Example Choices:\n\n{example_choices_dynamic}\n\n")
                    f.write("=" * 60 + "\n")
                # save the accumulated token usage
                f.write(f"Accumulated Token Usage:\n\n{json.dumps(accumulated_usage, indent=4, ensure_ascii=False)}\n\n")
                f.write("=" * 60 + "\n")
                # save the list of reasoning summaries
                f.write(f"Reasoning Summary List:\n\n{json.dumps(reasoning_summary_list, indent=4)}\n\n")
                f.write("=" * 60 + "\n")
                # save the flattened reasoning summary string
                reasoning_summary_str = "\n\n".join(reasoning_summary_list)
                f.write(f"Reasoning Summary String:\n\n{reasoning_summary_str}\n\n")
                f.write("=" * 60 + "\n")
                # save the model final response text
                f.write(f"Model Response Text:\n\n{response_text}\n\n")
                f.write("=" * 60 + "\n")
                f.write(f"Conversation History:\n\n{json.dumps(messages, ensure_ascii=False, indent=4)}\n\n")
                f.write("=" * 60 + "\n")
                # save the token usage list for all queries
                f.write(f"Token Usage List:\n\n{json.dumps(usage_list, indent=4, ensure_ascii=False)}")

        # Add the assistant response to the context
        messages.append({"role": "assistant", "content": [{"type": "output_text", "text": response_text}]})

        # Also make the prediction directory if it doesn't exist
        os.makedirs(pred_dir, exist_ok=True)

        # Validate the model prediction
        pattern = r"<<<(.*?)>>>"
        matches = re.findall(pattern, response_text, re.DOTALL)
        if matches:
            model_prediction = matches[-1]
            model_prediction = re.sub(r"\s+", " ", model_prediction).strip()
            print("=" * 60)
            print(f"Instance {instance_idx} pred: {model_prediction}")
            print("-" * 60)

            error_message = validator.validate(model_prediction, problem_text, str(instance_idx))
            print(f"Instance {instance_idx} error_message: {error_message}")
            print("-" * 60)

            # if no error message, we just save the result and exit the query loop
            if error_message == "" or error_message is None:
                result_file = os.path.join(pred_dir, str(instance_idx) + ".json")
                with open(result_file, "w", encoding="utf-8") as f:
                    print(f"Instance {instance_idx} writing result...")
                    print("=" * 60)
                    json.dump(
                        {
                            "prediction": model_prediction,
                            # will add ground truth later during evaluation
                        },
                        f,
                        ensure_ascii=False,
                    )
                return True  # Success, exit the query loop

            # otherwise, we need to provide feedback to the model, and continue the query loop
            feedback = lean_error(error_message)
            if "unknown identifier" in error_message:
                feedback += (
                    "\n\nYou should only use the provided relations and axioms, and you must declare all Points, Lines, and Circles "
                    "that you will use in the formal statement (see Syntax Tip 1 and Syntax Tip 2 in the guidelines). "
                    "When you see an error message that contains 'unknown identifier', "
                    "it means that you have either used some relations that are not provided in the guidelines, "
                    "or you have forgotten to declare some Points, Lines, or Circles that are used in the formalized statement. "
                    "Please double-check and fix this, or your formalized statement won't compile!"
                )
            elif "Unexpected expression" in error_message:
                feedback += (
                    "\n\nYour formalized statement has declared extra variables "
                    "that are not used in the formalized statement (see Syntax Tip 3 in the guidelines)."
                    "Please double-check and fix this, or your formalized statement won't compile!"
                )
            elif "unexpected token ')'; expected ':'" in error_message:
                feedback += (
                    "\n\nA formalized angle ∠ A:B:C always expects three point identifiers separated by colons (see Syntax Tip 4 in the guidelines)."
                    "Even though you will see the English expressions like angle Y, but ∠ Y is not a valid formalization! "
                    "You should formalize it into ∠ X:Y:Z where X, Y, and Z are the three points that form the angle. "
                    "When you see an error message like 'unexpected token ')'; expected ':'' "
                    "it means that you have not provided the correct number of identifiers for the angle, "
                    "or you need to surround the angle with parentheses like (∠ X:Y:Z) to avoid ambiguity."
                    "Please double-check and fix this, or your formalized statement won't compile!"
                )
            elif "Variable naming violation" in error_message:
                feedback += (
                    "\n\nYour formalized statement doesn't follow the expected Variable Naming Guidelines (see Guidelines #4). "
                    "When you see an error message like 'Variable naming violation' "
                    "it means that you have used a variable name that is not in the English problem statement, or have extra prefix/suffix. "
                    "Please double-check and fix this, or your formalized statement won't pass the validation!"
                )
            elif "Variable Declaration Error" in error_message:
                feedback += (
                    "\n\nYour formalized statement doesn't follow the expected Variable Declaration Guidelines (see Guidelines #1). "
                    "You should only use 1 universal quantifier at the start of the formalized statement, "
                    "and all variable declarations must be placed in parentheses after the universal quantifier. "
                    "For different types of variables, you should put them in different parentheses. "
                    "For example, if the English statement contains 'The points A, B are on line AB', "
                    "then you should declare (A B : Point) (AB : Line) in the formalized statement. "
                    "Please double-check and fix this, or your formalized statement won't pass the validation!"
                )
            elif "tactic 'introN' failed" in error_message:
                feedback += (
                    "\n\nYour formalized statement doesn't follow the expected Proposition Format (see Guidelines #1). "
                    "Please double-check and fix this, or your formalized statement won't pass the validation!"
                )
            elif "no goals to be solved" in error_message:
                feedback += (
                    "\n\nYour formalized statement has a trivially true conclusion without using any given premises (e.g. True, A = A, etc.)"
                    "The input English statement is always a theorem with a **non-trivial conclusion** that requires the use of given premises! "
                    "Please double-check and fix this, or your formalized statement won't pass the validation!"
                )
            elif "test_premises_contradictory" in error_message:
                feedback += (
                    "\n\nYour formalized statement has contradictory premises, which is not what we want. "
                    "The input English statement is always a theorem with **non-contradictory premises**! "
                    "It's very likely that you have passed parameters in wrong orders "
                    "for relations like `between`, `formTriangle`, `formParallelogram`, etc. where order and correspondence of arguments matters! "
                    "Please double-check and fix this, or your formalized statement won't pass the validation!"
                )
            elif "test_conclusions_valid" in error_message:
                feedback += (
                    "\n\nYour formalized statement has a trivially true conclusion without using any given premises, which is not what we want. "
                    "The input English statement is always a theorem with a **non-trivially true conclusion** "
                    "that requires the use of the given premises! "
                    "Please double-check and fix this, or your formalized statement won't pass the validation!"
                )
            elif "test_false" in error_message:
                feedback += (
                    "\n\nYour formalized statement is false under the background theory, which is not what we want. "
                    "The input English statement is always a **true theorem**! "
                    "Please double-check and fix this, or your formalized statement won't pass the validation!"
                )
            elif "Checker error when extracting quantified variables" in error_message:
                feedback += (
                    "\n\nYour formalized statement has a checker error, likely due to invalid Formalized Statement Format (see Guidelines #1). "
                    "Your formalized statement must be of the form <<< ∀ (...), P_1 ∧ P_2 ... ∧ P_n → Q_1 ∧ Q_2 ... ∧ Q_m >>>. "
                    "All variable declarations must be placed in parentheses after the universal quantifier. "
                    "You shouldn't declare variables or use quantifiers in any other places!"
                    "Please double-check and fix this, or your formalized statement won't pass the validation!"
                )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
        else:
            messages.append({"role": "user", "content": [{"type": "input_text", "text": parse_error()}]})

    print(f"Instance {instance_idx} failed after {num_query} attempts")
    print("=" * 60)
    return False


async def autoformalize_batch_instances_vanilla(
    task_list: list[tuple[str, int, int, str, str, Validator]],
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    llm: UnifiedModel,
    client: Any,
    args: argparse.Namespace,
) -> list[bool]:
    # Process all instances at once
    result_list: list[bool] = []

    print(f"🚀 Starting async processing of {len(args.testing_idx)} instances with max {args.num_async} concurrent tasks ...")

    # Create tasks for all instances
    async_task_list = []

    for task in task_list:
        category, run_idx, instance_idx, pred_dir, response_dir, validator = task
        async_task = autoformalize_single_instance(
            category, run_idx, instance_idx, system_content, example_content, example_messages, pred_dir, response_dir, validator, llm, client, args
        )
        async_task_list.append(async_task)

    # Process tasks with concurrency limit
    semaphore = asyncio.Semaphore(args.num_async)
    coros = [process_with_semaphore(t, semaphore) for t in async_task_list]
    futures = [asyncio.create_task(coro) for coro in coros]

    # Choose `asyncio.as_completed` over `asyncio.gather` to stream the results
    # we don't need to keep the original order in the task list
    # since `process_single_instance` will save our results to files with ordered names
    for future in tqdm.as_completed(
        futures, total=len(task_list), desc=f"Category {args.category}", unit="instance", position=0, leave=True, ncols=100, dynamic_ncols=True
    ):
        result = await future
        result_list.append(result)

    return result_list


async def autoformalize_batch_instances_caching(
    task_list: list[tuple[str, int, int, str, str, Validator]],
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    llm: UnifiedModel,
    client: Any,
    args: argparse.Namespace,
) -> list[bool]:
    # Process the first instance individually to enable prompt caching
    result_list: list[bool] = []

    print(f"🚀 Processing first instance in category {task_list[0][0]} and run {task_list[0][1]} to enable prompt caching...")
    # Fetch the first instance's information
    first_category, first_run_idx, first_instance_idx, pred_dir, response_dir, validator = task_list[0]
    # Get the first instance's formalization
    first_result = await autoformalize_single_instance(
        first_category,
        first_run_idx,
        first_instance_idx,
        system_content,
        example_content,
        example_messages,
        pred_dir,
        response_dir,
        validator,
        llm,
        client,
        args,
    )
    result_list.append(first_result)

    # Process the rest of the instances using the vanilla function
    if len(task_list) > 1:
        remaining_results = await autoformalize_batch_instances_vanilla(
            task_list[1:], system_content, example_content, example_messages, llm, client, args
        )
        result_list.extend(remaining_results)

    return result_list


async def autoformalize_batch_instances(
    task_list: list[tuple[str, int, int, str, str, Validator]],
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    llm: UnifiedModel,
    args: argparse.Namespace,
) -> list[bool]:
    # Determine which function to call based on caching preference
    target_function = autoformalize_batch_instances_caching if args.enable_caching else autoformalize_batch_instances_vanilla

    # Initialize the client if needed
    model_id = llm.model_id

    # Need to create client for Bedrock models
    if model_id in (BEDROCK_CLAUDE_MODEL_LIST + BEDROCK_CLAUDE_THINKING_MODEL_LIST):
        async with llm.async_session.client(**llm.client_args) as client:
            return await target_function(task_list, system_content, example_content, example_messages, llm, client, args)
    # No need to create client for OpenAI, OpenRouter models
    else:
        client = None  # no need to create client for OpenRouter models
        return await target_function(task_list, system_content, example_content, example_messages, llm, client, args)


def autoformalize_batch_instances_sync(
    task_list: list[tuple[str, int, int, str, str, Validator]],
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    llm: UnifiedModel,
    args: argparse.Namespace,
) -> list[bool]:
    """Synchronous wrapper for async autoformalize_batch_instances"""
    return asyncio.run(autoformalize_batch_instances(task_list, system_content, example_content, example_messages, llm, args))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--dataset",
        type=str,
        choices=["UniGeo"],
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
        "--reasoning",
        type=str,
        choices=["text-only", "multi-modal"],
        required=True,
        help="Reasoning Type",
    )
    parser.add_argument("--num_query", type=int, default=5, help="Maximum number of query per instance")
    parser.add_argument("--num_examples", type=int, default=0, help="Number of examples")
    parser.add_argument("--example_choices", type=str, nargs="+", default=["none"], help="Choices of in-context examples")
    parser.add_argument("--example_format", type=str, choices=["content", "messages"], default="content", help="Format of in-context examples")
    parser.add_argument(
        "--cot_for_reasoning_models",
        type=str,
        choices=["no", "minimal", "full"],
        default="full",
        help="Level of detail of in-context CoT demonstrations for reasoning models",
    )
    parser.add_argument("--num_process", type=int, default=5, help="Maximum number of processes")
    parser.add_argument("--num_async", type=int, default=20, help="Maximum number of async tasks for each process")
    parser.add_argument("--enable_caching", action="store_true", default=True, help="Enable prompt caching by processing first instance individually")
    parser.add_argument("--temperature", type=float, default=0.2, help="Temperature for the model")
    parser.add_argument("--num_run", type=int, default=5, help="Number of runs for sampling")
    parser.add_argument("--root_dir", type=str, default=ROOT_DIR, help="Root directory")
    parser.add_argument("--result_dir_name", type=str, default="result", help="Name of the result directory")
    parser.add_argument(
        "--relations_file",
        type=str,
        default="Relations_barebone",
        help="Name of the UniGeo-specific relations file under the directory, for simplification of the model prediction",
    )
    parser.add_argument(
        "--dsl_doc",
        type=str,
        default="doc_barebone.txt",
        help="Name of the DSL documentation file under the directory",
    )
    parser.add_argument(
        "--reuse_responses",
        action="store_true",
        default=False,
        help=(
            "Reuse saved response .txt files when present (skipping the LLM call) and only "
            "call the LLM for missing instances. Preserves existing responses, re-runs only "
            "validation. Only valid for single-query methods (e.g. 1_direct)."
        ),
    )
    parser.add_argument(
        "--max_instances",
        type=int,
        default=0,
        help=(
            "If > 0, only process the first N problem instances (for fast smoke tests). "
            "0 (default) means all instances. Does NOT affect a normal full run."
        ),
    )

    args = parser.parse_args()

    # The argument `num_examples` must be non-negative
    if args.num_examples < 0:
        raise ValueError(f"`num_examples` must be non-negative, but got {args.num_examples}")

    # The arguments `example_choices` must be consistent with `num_examples`
    first_choice = args.example_choices[0]
    if (first_choice == "none" and args.num_examples != 0) or (
        first_choice != "none" and first_choice != "dynamic" and len(args.example_choices) != args.num_examples
    ):
        raise ValueError(f"`example_choices` must be consistent with `num_examples`, but got {args.example_choices} and {args.num_examples}")

    # For UniGeo, each example choice must be in the format of "category-num",
    # with category in ["Parallel", "Triangle", "Quadrilateral", "Congruent", "Similarity"] and num in ["1", "2", "3", "4", "5"]
    # A special case is "dynamic", which means 1-shot examples are dynamically selected for each instance
    if args.dataset == "UniGeo" and first_choice != "none" and first_choice != "dynamic":
        for choice in args.example_choices:
            # check the format of the choice using regex
            pattern = r"^[A-Z][a-z]+-\d$"
            if not re.match(pattern, choice):
                raise ValueError(f"Invalid example choice: {choice}")
            # split the choice into category and num
            category, num = choice.split("-")
            if category not in ["Parallel", "Triangle", "Quadrilateral", "Congruent", "Similarity"] or num not in ["1", "2", "3", "4", "5"]:
                raise ValueError(f"Invalid example choice: {choice}")

    # For Book, each example choice must be in the format of "num"
    # with num in ["1", "2", "3", "4", "5"]
    if args.dataset == "Book" and first_choice != "none":
        for choice in args.example_choices:
            if choice not in ["1", "2", "3", "4", "5"]:
                raise ValueError(f"Invalid example choice: {choice}")

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
    else:  # Book / Euclid's Elements
        args.testing_idx = [i for i in range(1, 49) if i not in [2, 6, 12, 32, 42]]

    # Smoke-test knob: cap the number of instances. No effect on a full run (default 0).
    if args.max_instances and args.max_instances > 0:
        args.testing_idx = args.testing_idx[: args.max_instances]
        print(f"⚡ --max_instances={args.max_instances}: limiting to instances {args.testing_idx}")

    print("------------------------------------------------------------")
    print("args: ", args)
    print("------------------------------------------------------------")

    # Construct directory name for in-context examples setting
    example_choices_str = ""
    if args.num_examples == 0:
        example_choices_str = "0-shot"
    elif args.num_examples == 1:
        example_choices_str = "1-shot_" + args.example_choices[0]
    else:
        flattened_example_choices = "+".join(args.example_choices)
        example_choices_str = str(args.num_examples) + "-shot_" + flattened_example_choices

    # Construct instruction
    system_content = construct_instruction(args)
    # Construct static in-context examples, if `num_examples` > 0 and `example_choices` is not "dynamic"
    example_content: Content = []
    example_messages: Messages = []
    if args.num_examples > 0 and first_choice != "dynamic":
        example_content, example_messages = construct_example_messages(args.dataset, args.num_examples, args.example_choices, args, True)

    # Initialize the LLM Class
    if args.model in OPENAI_GPT_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://api.openai.com/v1",
            max_output_tokens=6144,
            temperature=args.temperature,
        )
    elif args.model in OPENAI_O_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://api.openai.com/v1",
            max_output_tokens=12_288,
            temperature=1.0,  # o-series models only support temperature=1.0
            reasoning_effort=args.openai_reasoning_effort,  # default is "medium"
            reasoning_summary="detailed",  # default is "auto"
        )
    elif args.model in OPENAI_GPT5_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://api.openai.com/v1",
            max_output_tokens=16_384,
            temperature=1.0,  # gpt-5 models only support temperature=1.0
            verbosity="medium",
            reasoning_effort=args.openai_reasoning_effort,
            reasoning_summary="detailed",
        )
    elif args.model.startswith("us.anthropic.claude-opus-4-8"):
        # Claude Opus 4.8 (plain or "-thinking-<effort>"). Routed before the generic Bedrock
        # branches. 4.8 deprecates temperature (must NOT be passed); the thinking shape and
        # effort level are derived from the model ID inside inference_bedrock.format_request.
        llm = create_unified_model(
            model_id=args.model,
            max_tokens=16_384,
            cache_prompt="default",
        )
    elif args.model in BEDROCK_CLAUDE_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            max_tokens=6144,
            temperature=args.temperature,
            cache_prompt="default",
        )
    elif args.model in BEDROCK_CLAUDE_THINKING_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            max_tokens=16_384,
            temperature=1.0,  # Anthropic reasoning/thinking models only support temperature=1.0
            cache_prompt="default",
            claude_thinking_type="enabled",
            claude_thinking_budget_tokens=12_288,
        )
    elif args.model in OPENROUTER_CLAUDE_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://openrouter.ai/api/v1",
            max_tokens=6144,
            temperature=args.temperature,
            provider={"only": ["anthropic"]},
        )
    elif args.model in OPENROUTER_CLAUDE_THINKING_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://openrouter.ai/api/v1",
            max_tokens=16_384,
            temperature=1.0,  # Anthropic reasoning/thinking models only support temperature=1.0
            exclude_reasoning_output=False,
            include_usage=True,
            reasoning_budget=12_288,
            provider={"only": ["anthropic"]},
        )
    elif args.model in OPENROUTER_QWEN3_MODEL_LIST:
        if args.model == "qwen/qwen3-30b-a3b-instruct-2507":
            provider = "nebius/fp8"
        elif args.model in ["qwen/qwen3-8b", "qwen/qwen3-coder"]:
            provider = "novita/fp8"
        else:
            provider = "deepinfra/fp8"
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://openrouter.ai/api/v1",
            max_tokens=6144,
            temperature=args.temperature,
            enable_reasoning=False,  # Doesn't have any effect now, just to make sure in case openrouter api changes
            provider={"only": [provider]},
        )
    elif args.model in OPENROUTER_QWEN3_THINKING_MODEL_LIST:
        if args.model == "qwen/qwen3-8b-thinking":
            provider = "novita/fp8"
        else:
            provider = "deepinfra/fp8"
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://openrouter.ai/api/v1",
            max_tokens=16_384,
            temperature=1.0,  # Qwen3 supports different temperature values, set to 1.0 to compare with other reasoning models
            exclude_reasoning_output=False,
            include_usage=True,
            reasoning_budget=12_288,
            provider={"only": [provider]},
        )
    elif args.model in OPENROUTER_GEMMA3_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://openrouter.ai/api/v1",
            max_tokens=6144,
            temperature=args.temperature,
            provider={"only": ["deepinfra/bf16"]},
        )
    elif args.model in OPENROUTER_GPT_OSS_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://openrouter.ai/api/v1",
            max_tokens=16_384,
            temperature=1.0,  # gpt-oss supports different temperature values, set to 1.0 to compare with other reasoning models
            exclude_reasoning_output=False,
            include_usage=True,
            reasoning_effort=args.openai_reasoning_effort,
            provider={"only": ["deepinfra/fp4"]},
        )
    elif args.model in OPENROUTER_DEEPSEEK_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://openrouter.ai/api/v1",
            max_tokens=6144,
            temperature=args.temperature,
            enable_reasoning=False,  # Doesn't have any effect now, just to make sure in case openrouter api changes
            provider={"only": ["deepinfra/fp4"]},
        )
    elif args.model in OPENROUTER_DEEPSEEK_THINKING_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="https://openrouter.ai/api/v1",
            max_tokens=16_384,
            temperature=1.0,  # DeepSeekV3.1 supports different temperature values, set to 1.0 to compare with other reasoning models
            exclude_reasoning_output=False,
            include_usage=True,
            reasoning_budget=12_288,
            provider={"only": ["deepinfra/fp4"]},
        )
    elif args.model in LOCAL_VLLM_MODEL_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="http://localhost:8000/v1",
            max_tokens=1024,
            temperature=args.temperature,
        )
    elif args.model in LOCAL_VLLM_MODEL_NEW_LIST:
        llm = create_unified_model(
            model_id=args.model,
            base_url="http://localhost:8000/v1",
            max_tokens=6144,
            temperature=args.temperature,
        )
    else:
        raise ValueError(f"Invalid model: {args.model}")

    # Create base directories for all categories
    model_dir_name = f"{args.model}_{llm.get_config()['reasoning_effort']}" if llm.get_config().get("reasoning_effort") else args.model

    tmp_dir_base = os.path.join(
        args.root_dir,
        "tmp",
        "validate",
        args.result_dir_name,
        args.dataset,
        args.reasoning,
        args.method,
        model_dir_name,
        example_choices_str,
    )
    response_dir_base = os.path.join(
        args.root_dir,
        args.result_dir_name,
        "response",
        args.dataset,
        args.reasoning,
        args.method,
        model_dir_name,
        example_choices_str,
    )
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

    if args.reuse_responses:
        # REUSE MODE: preserve saved responses (the inputs we reuse). Still clear the
        # prediction dir (partial JSONs from a crashed run) and tmp dir (possibly
        # OOM-poisoned Lean/SMT temp files) so re-validation starts from clean state.
        print("♻️  REUSE MODE: preserving response dir, clearing predictions + tmp")
        if os.path.exists(pred_dir_base):
            print(f"🔨 Removing old prediction files in {pred_dir_base} ...")
            shutil.rmtree(pred_dir_base)
        if os.path.exists(tmp_dir_base):
            print(f"🔨 Removing old tmp files in {tmp_dir_base} ...")
            shutil.rmtree(tmp_dir_base)
    # If old predictions and responses exist, prompt the user to confirm the overwrite
    elif os.path.exists(pred_dir_base) and os.path.exists(response_dir_base):
        print(f"Prediction directory: {pred_dir_base}")
        print(f"Response directory: {response_dir_base}")
        confirm = input("Do you want to remove old files in the prediction and response directories? (y/n): ")
        if confirm.lower() != "y":
            print("Aborting removal of old files.")
            return
        # If yes, continue to remove the base directories entirely
        print(f"🔨 Removing old files & subdirectories in {pred_dir_base} ...")
        shutil.rmtree(pred_dir_base)
        print(f"🔨 Removing old files & subdirectories in {response_dir_base} ...")
        shutil.rmtree(response_dir_base)
        print(f"🔨 Removing old files & subdirectories in {tmp_dir_base} ...")
        shutil.rmtree(tmp_dir_base)

    # Create base directories
    print(f"📂 Creating prediction directories for all categories: {pred_dir_base}")
    os.makedirs(pred_dir_base, exist_ok=True)
    print(f"📂 Creating response directories for all categories: {response_dir_base}")
    os.makedirs(response_dir_base, exist_ok=True)
    print(f"📂 Creating tmp directories for all categories: {tmp_dir_base}")
    os.makedirs(tmp_dir_base, exist_ok=True)

    # track total successful and failed instances
    total_successful = 0
    total_failed = 0

    # Create task list
    task_list: list[tuple[str, int, int, str, str, Validator]] = []
    for category in args.category:
        for instance_idx in args.testing_idx:
            # We add tasks in this order, so that exactly the same category-instance combination (but different runs)
            # are likely to be sent to the same process, which helps prompt caching
            for run_idx in range(1, args.num_run + 1):
                # Create directories for this category and this run
                tmp_dir = os.path.join(tmp_dir_base, category, f"run_{run_idx}")
                response_dir = os.path.join(response_dir_base, category, f"run_{run_idx}")
                pred_dir = os.path.join(pred_dir_base, category, f"run_{run_idx}")
                # Create validator for this category and this run
                validator = Validator(
                    root_dir=args.root_dir,
                    tmp_dir=tmp_dir,
                    relations_file=args.relations_file,
                )
                # Create tasks for each instance in this category and this run
                task_list.append((category, run_idx, instance_idx, pred_dir, response_dir, validator))

    # Split the task into consecutive chunks for each process
    # If the number of tasks is less than the number of processes, adjust the number of processes, and assign 1 task per process
    if len(task_list) < args.num_process:
        args.num_process = len(task_list)
        chunk_size = 1
        remainder = 0
    else:
        # UniGeo has 100 problem instances * X run each, we use 100 processes by default,
        # so the chunk size is X
        chunk_size = len(task_list) // args.num_process
        remainder = len(task_list) % args.num_process

    task_chunk_list = []
    start_idx = 0
    # We will assign the same problem (different runs) to the same process, 
    # so that we can leverage prompt caching
    for i in range(args.num_process):
        # Add 1 extra task to first 'remainder' processes to distribute evenly
        current_chunk_size = chunk_size + (1 if i < remainder else 0)
        end_idx = start_idx + current_chunk_size
        task_chunk_list.append(task_list[start_idx:end_idx])
        start_idx = end_idx

    # Process each process in parallel
    result_chunk_list = Parallel(
        n_jobs=args.num_process,
        backend="loky",
        verbose=10,  # More detailed progress (0=quiet, 10=very verbose, 50=debug)
        batch_size=1,  # One instance per parallel process
        max_nbytes=None,  # No memory limit
        pre_dispatch="2*n_jobs",  # Pre-dispatch tasks for better performance
    )(
        delayed(autoformalize_batch_instances_sync)(process_task_list, system_content, example_content, example_messages, llm, args)
        for process_task_list in task_chunk_list
    )

    # Flatten the multi-process result list
    result_list = [item for sublist in result_chunk_list for item in sublist]

    # Count successful and failed instances
    successful = sum(1 for result in result_list if result is True)
    failed = len(result_list) - successful
    total_successful += successful
    total_failed += failed

    if failed > 0:
        print(f"❌ Categories {args.category} completed! Success: {successful}, Failure: {failed}")
    elif successful > 0:
        print(f"✅ Categories {args.category} completed! Success: {successful}, Failure: {failed}")
    else:
        print(f"❌ Categories {args.category} completed! Success: {successful}, Failure: {failed}")

    if total_failed > 0:
        print(f"❌ Total Successful: {total_successful}, Total Failure: {total_failed}")
    else:
        print(f"✅ Total Successful: {total_successful}, Total Failure: {total_failed}")


if __name__ == "__main__":
    main()
