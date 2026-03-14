# pylint: disable=R0903,R0912,R0916,R0801,R1714,W0603,C0302


# Standard Library Modules
import argparse
import asyncio
import inspect
import json
import os
import random
import re
import shutil
import sys
import ast
from typing import Any, Awaitable, Optional, Dict, List

# External Modules
import json5
from joblib import Parallel, delayed
from loguru import logger
from tqdm.asyncio import tqdm as async_tqdm
from tqdm.auto import tqdm as sync_tqdm
import joblib
from contextlib import contextmanager
from types import SimpleNamespace

# Internal Modules
from path import (
    EXAMPLE_DIR,
    ROOT_DIR,
)
from afc import (
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
from afc.type_defs import Content, Messages
# Dynamic validator import based on dataset
def get_validator_class(dataset: str):
    """Get the appropriate validator class based on dataset type."""
    if dataset in ["ProofNet", "connf", "DSL"]:
        from afc.proofnet import Validator as ProofNetValidator
        return ProofNetValidator
    else:
        raise ValueError(f"Unsupported dataset: {dataset}. Only ProofNet, connf, and DSL are supported.")


# Fix random seed
random.seed(42)


# Constants
REASONING_MODEL_SET = set(OPENAI_O_MODEL_LIST +BEDROCK_CLAUDE_THINKING_MODEL_LIST + OPENROUTER_GPT_OSS_MODEL_LIST)
LOCAL_VLLM_MODEL_LIST = [
    "FrenzyMath/Herald_translator",
    "AI-MO/Kimina-Autoformalizer-7B",
    "huawei-ai4math/Mathesis-Autoformalizer",
    "huawei-ai4math/Mathesis-Autoformalizer-HPO"
]


def load_config_into_args(args: argparse.Namespace, parser: argparse.ArgumentParser) -> argparse.Namespace:
    """Load a JSON/JSON5 config file if provided via --config and merge into args.

    CLI args take precedence over config values. We treat values equal to the
    parser defaults (or None) as not provided and can be overwritten by config.
    """
    cfg_path = getattr(args, 'config', None)
    if not cfg_path:
        return args
    try:
        with open(cfg_path, 'r', encoding='utf-8') as f:
            cfg = json5.load(f)
    except Exception:
        return args

    # Build defaults map
    defaults = {}
    for action in parser._actions:
        if action.dest != 'help' and action.dest:
            defaults[action.dest] = action.default

    for k, v in cfg.items():
        if not hasattr(args, k):
            continue
        cur = getattr(args, k)
        # If user did not override (cur is None or equals default), use config
        if cur is None or (k in defaults and cur == defaults[k]):
            setattr(args, k, v)
    return args


def configure_logging(quiet: bool) -> None:
    """Configure global loguru logging sinks based on quiet flag."""
    logger.remove()
    if not quiet:
        logger.add(sys.stdout, level="INFO")


def instantiate_validator(ValidatorClass, *, root_dir: str, tmp_dir: str, relations_file: str, quiet: bool):
    """Instantiate validator with optional quiet flag when supported."""
    kwargs = dict(
        root_dir=root_dir,
        tmp_dir=tmp_dir,
        # IMPORTANT: load correct relations file!
        relations_file=relations_file,
        quiet=quiet
    )
    try:
        init_params = inspect.signature(ValidatorClass.__init__).parameters
        if 'quiet' in init_params:
            kwargs['quiet'] = quiet
    except (ValueError, TypeError):
        pass
    return ValidatorClass(**kwargs)


def _log_info(args: argparse.Namespace, message: str) -> None:
    if not getattr(args, 'quiet', False):
        logger.info(message)


def _log_warning(args: argparse.Namespace, message: str) -> None:
    if not getattr(args, 'quiet', False):
        logger.warning(message)


def _log_error(args: argparse.Namespace, message: str) -> None:
    if not getattr(args, 'quiet', False):
        logger.error(message)


def _resolve_dsl_relations_path(args: argparse.Namespace) -> str:
    instructions_dir = os.path.join(os.path.dirname(__file__), "instructions", "dsl_instructions")
    exp_type = getattr(args, "experiment_type", "barebone")
    mapping = {
        "oracle": "Relations_oracle.lean",
        "learned": "Relations_learned.lean",
    }
    rel_name = mapping.get(exp_type)
    if not rel_name:
        return ""
    candidate = os.path.join(instructions_dir, rel_name)
    return candidate if os.path.exists(candidate) else ""


def _relations_path_for_dataset(args: argparse.Namespace, dataset: Optional[str] = None) -> str:
    target_dataset = dataset or getattr(args, "dataset", "")
    if target_dataset == "DSL":
        return getattr(args, "dsl_relations_path", "")
    if target_dataset in {"ProofNet", "connf"}:
        return ""
    return getattr(args, "relations_file", "")


@contextmanager
def _joblib_progress(tqdm_object):
    class TqdmBatchCompletionCallback(joblib.parallel.BatchCompletionCallBack):
        def __call__(self, *args, **kwargs):
            tqdm_object.update(n=self.batch_size)
            return super().__call__(*args, **kwargs)

    old_callback = joblib.parallel.BatchCompletionCallBack
    joblib.parallel.BatchCompletionCallBack = TqdmBatchCompletionCallback
    try:
        yield
    finally:
        joblib.parallel.BatchCompletionCallBack = old_callback


def construct_instruction(args: argparse.Namespace) -> Content:
    # Construct the instruction head based on the dataset and reasoning type
    if args.dataset in ["ProofNet", "connf"]:
        instructions_dir = os.path.join(os.path.dirname(__file__), "instructions")
        instruction_head = (
            "You are given an English Statement of a mathematical theorem. "
            "Your task is to formalize this statement into Lean 4 code using Mathlib4. "
            "Target environment: Lean 4.7.0-rc2 with Mathlib4. Do NOT use Lean 3 or deprecated identifiers. "
            "Use only current Lean 4/Mathlib4 names and notations.\n\n"
        )
        pipeline_prompt = (
            "Your task is to formalize the English Statement into a formal theorem in Lean 4 "
            "using the Mathlib library and no other libraries, strictly adhering to the following formal definitions and guidelines.\n\n"
        )
        if args.method == "1_direct":
            with open(os.path.join(instructions_dir, "1_direct.txt"), "r", encoding="utf-8") as f:
                instruction = instruction_head + pipeline_prompt + "\n\n" + f.read()
        elif args.method == "2_self-refine":
            with open(os.path.join(instructions_dir, "2_self-refine.txt"), "r", encoding="utf-8") as f:
                instruction = instruction_head + pipeline_prompt  + "\n\n" + f.read()
        elif args.method == "3_semi-formalize":
            pipeline_prompt = (
                "Your task is to first semi-formalize the English Statement into a json-style structure "
                "(see Guidlines #2), and then convert the Semi-Formalized Structure into a formal statement in Lean 4 "
                "strictly adhering to the following formal definitions and guidelines.\n\n"
            )
            with open(os.path.join(instructions_dir, "3_semi-formalize.txt"), "r", encoding="utf-8") as f:
                instruction = instruction_head + pipeline_prompt  + "\n\n" + f.read()
        elif args.method == "4_formalized-structure":
            pipeline_prompt = (
                "Your task is to first semi-formalize the English Statement into a json-style structure "
                "(see Guidlines #2), then formalize each clause in the Semi-Formalized Structure resulting in a Formalized Structure (see Guidlines #3), "
                "and finally convert the Formalized Structure into a formal statement in Lean 4 "
                "strictly adhering to the following formal definitions and guidelines.\n\n"
            )
            with open(os.path.join(instructions_dir, "4_formalized-structure.txt"), "r", encoding="utf-8") as f:
                instruction = instruction_head + pipeline_prompt  + "\n\n" + f.read()
        else:
            raise ValueError(f"Invalid method: {args.method}")

    elif args.dataset == "DSL":
        instructions_dir = os.path.join(os.path.dirname(__file__), "instructions")
        instruction_head = (
            "You are given an English Statement of a mathematical theorem. "
            "Target environment: Lean 4.7.0-rc2 with Mathlib4. Do NOT use Lean 3 or deprecated identifiers. "
            "Use only current Lean 4/Mathlib4 names and notations.\n\n\n"
        )
        pipeline_prompt = (
            "Your task is to formalize the English Statement into a formal theorem in Lean 4 "
            "using the Mathlib library and no other libraries, strictly adhering to the following formal definitions and guidelines.\n\n\n"
        )

        # Load DSL-specific instructions based on experiment type
        dsl_instructions_dir = os.path.join(instructions_dir, "dsl_instructions")
        if args.experiment_type == "oracle":
            relations_file = os.path.join(dsl_instructions_dir, "Relations_oracle.lean")
        elif args.experiment_type == "learned":
            relations_file = os.path.join(dsl_instructions_dir, "Relations_learned.lean")
        else:  # barebone
            relations_file = None

        dsl_doc = ""
        if relations_file and os.path.exists(relations_file):
            with open(relations_file, "r", encoding="utf-8") as f:
                dsl_relations = f.read()
            dsl_doc = f"Here are an extra set of helpers you can **DIRECTLY USE** in addition to Mathlib:\n\n{dsl_relations}\n\n"

        if args.method == "1_direct":
            with open(os.path.join(instructions_dir, "1_direct.txt"), "r", encoding="utf-8") as f:
                instruction = instruction_head + pipeline_prompt + dsl_doc + "\n\n" + f.read()
        elif args.method == "2_self-refine":
            with open(os.path.join(instructions_dir, "2_self-refine.txt"), "r", encoding="utf-8") as f:
                instruction = instruction_head + pipeline_prompt + dsl_doc + "\n\n" + f.read()
        elif args.method == "3_semi-formalize":
            pipeline_prompt = (
                "Your task is to first semi-formalize the English Statement into a json-style structure "
                "(see Guidlines #2), and then convert the Semi-Formalized Structure into a formal statement in Lean 4 "
                "strictly adhering to the following formal definitions and guidelines.\n\n"
            )
            with open(os.path.join(instructions_dir, "3_semi-formalize.txt"), "r", encoding="utf-8") as f:
                instruction = instruction_head + pipeline_prompt + dsl_doc + "\n\n" + f.read()
        elif args.method == "4_formalized-structure":
            pipeline_prompt = (
                "Your task is to first semi-formalize the English Statement into a json-style structure "
                "(see Guidlines #2), then formalize each clause in the Semi-Formalized Structure resulting in a Formalized Structure (see Guidlines #3), "
                "and finally convert the Formalized Structure into a formal statement in Lean 4 "
                "strictly adhering to the following formal definitions and guidelines.\n\n"
            )
            with open(os.path.join(instructions_dir, "4_formalized-structure.txt"), "r", encoding="utf-8") as f:
                instruction = instruction_head + pipeline_prompt + dsl_doc + "\n\n" + f.read()
        else:
            raise ValueError(f"Invalid method: {args.method}")

    else:
        raise NotImplementedError("Currently, only ProofNet, connf, and DSL datasets are supported for autoformalization.")

    instruction_content = [{"type": "input_text", "text": instruction}]
    return instruction_content



# ---- Error-aware feedback for ProofNet (uses validator artifacts) ----
def _build_error_aware_feedback(
    *,
    dataset: str,
    validator: Any,
    instance_idx: int,
    raw_error: str,
) -> str:
    """Augment generic Lean error feedback with category-specific, ProofNet-targeted guidance.

    Reads validator's JSON classification if available, otherwise falls back to substring rules.
    """
    # Base generic feedback
    feedback = lean_error(raw_error)

    # Only ProofNet/connf/DSL currently supported for detailed mapping
    if dataset not in ["ProofNet", "connf", "DSL"]:
        return feedback

    # Try to load structured classification from validator logs
    meta = None
    try:
        error_base = f"{instance_idx}_lean-syntax_lean-syntax"
        err_json = os.path.join(getattr(validator, 'error_dir', ''), f"{error_base}.error.json")
        if os.path.isfile(err_json):
            with open(err_json, 'r', encoding='utf-8') as f:
                meta = json.load(f)
    except Exception:
        meta = None

    category = (meta or {}).get('category')
    tokens = (meta or {}).get('tokens', [])

    def add(lines: list[str]):
        nonlocal feedback
        feedback += "\n\n" + "\n".join(lines)

    # Category-driven tips
    if category == 'unknown_identifier' or category == 'unknown_constant':
        mapping = {
            'Convergent': "Use `Summable` for series, or `∃ l, Filter.Tendsto s Filter.atTop (𝓝 l)` for sequences.",
            'Function.IsFieldHom': "Use `RingHom` / `AlgHom` in Mathlib4.",
            'QuotientGroup.quotient': "Use `Subgroup.Quotient`.",
            'Metric.bounded': "Use `Bornology.IsBounded`.",
            'IsPerfect': "Use the set predicate `Set.Perfect` if applicable.",
            'Real.cbrt': "Avoid `Real.cbrt`; use `Real.rpow` with `1/3` or an equivalent formulation.",
            'Nat.padicValNat': "Check current Mathlib4 naming; padic valuation APIs have moved.",
            'Icc': "Use `Set.Icc` (and friends `Set.Ici`, `Set.Ioc`, `Set.Ioi`).",
            'Ioi': "Use `Set.Ioi` (and qualify all intervals with `Set.`).",
            'tendsto': "Use `Filter.Tendsto` and `Filter.atTop`.",
            'Perm': "Use `Equiv.Perm`.",
            'Set.card': "Use `Fintype.card` or `Nat.card` as appropriate.",
        }
        tips = [f"- {t}: {mapping.get(t, 'Check Mathlib4 naming/namespace; avoid Lean 3-era names.')}" for t in tokens]
        add([
            "Lean 4/Mathlib4: replace unknown identifiers with current APIs:",
            *(tips if tips else ["- Check current Mathlib4 identifiers and namespaces."])
        ])
    elif category == 'application_type_mismatch' or category == 'type_mismatch':
        add([
            "Type/domain fixes:",
            "- Types vs sets: do not write `y ∈ ℂ` / `x ∈ ℝ`; use `y : ℂ`, `x : ℝ`.",
            "- Integrals on ℝ: use `∫ x, …` or `∫ x in Set.univ, …`.",
            "- Euclidean space: replace `ℝ^m` by `EuclideanSpace ℝ (Fin m)`.",
            "- Norms vs complex abs: vectors use `‖x‖`; `Complex.abs` is only for `ℂ`.",
            "- Modular congruence: `Nat.ModEq` for ℕ, `Int.ModEq` for ℤ, or `ZMod n` coercions.",
            "- Finset indices: for `∑ i in Finset.range n, …`, functions should take `ℕ` indices.",
            "- Set difference/complement: operate in `Set` (e.g., `Uᶜ`, `Set.univ \\ U`).",
        ])
    elif category == 'parse_error':
        add([
            "Syntax fixes:",
            "- Expand binders: `∀ x ∈ S, ∀ y ∈ S, …` (avoid `∀ x y ∈ S`).",
            "- Avoid `∞`/`-∞` tokens in algebraic contexts; use bounds or limits.",
            "- Check colons/commas and binder shapes; prefer `fun x => …`.",
        ])
    elif category == 'invalid_field_notation' or category == 'invalid_field':
        add([
            "Field/structure APIs:",
            "- Use subgroup APIs (`Subgroup.center`, `Subgroup.centralizer`, `Subgroup.Quotient`).",
            "- For factorization extremes use `(Nat.factorization n).support.min' …`.",
        ])
    elif category == 'ambiguous':
        add([
            "Ambiguity fixes:",
            "- Disambiguate absolute value: `Real.abs` vs `Complex.abs`.",
            "- Add explicit types or namespaces when expressions are overloaded.",
        ])
    elif category == 'instance_synthesis_failed' or category == 'typeclass_stuck':
        add([
            "Typeclass instances:",
            "- Add required constraints in params (e.g., `[TopologicalSpace X]`, `[Field K]`).",
            "- Ensure proper imports and avoid Lean 3-era names.",
        ])
    else:
        # Fallback substring rules (legacy)
        err = (raw_error or '').lower()
        if 'unknown identifier' in err:
            add(["Check Mathlib4 names/namespaces; avoid deprecated identifiers."])
        if 'application type mismatch' in err or 'type mismatch' in err:
            add(["Check types vs sets; integrals over `Set.univ`; EuclideanSpace and norm usage."])
        if 'unexpected token' in err:
            add(["Fix binder syntax; expand `∀ x y ∈ S` properly; review punctuation."])

    # Always restate environment to reinforce
    add(["Environment: Lean 4.7.0-rc2 with Mathlib4. Use current Mathlib4 APIs only."])
    return feedback






def construct_example_messages(
    dataset: str, num_examples: int, example_choices: list[str], args: argparse.Namespace, add_header: bool
) -> tuple[Content, Messages]:
    # Only support DSL and ProofNet examples
    if dataset not in {"DSL", "ProofNet"}:
        raise NotImplementedError("construct_example_messages now only supports DSL and ProofNet.")

    # Output containers
    if add_header:
        example_header = "Here are some examples:\n\n" if num_examples > 1 else "Here is an example:\n\n"
        example_content: Content = [{"type": "input_text", "text": example_header}]
        example_messages: Messages = [{"role": "user", "content": [{"type": "input_text", "text": example_header}]}]
    else:
        example_content = []
        example_messages = [{"role": "user", "content": []}]

    # Treat each choice as filename stem (no category)
    example_keys: list[str] = list(example_choices)

    # Base directory for one-shot examples
    oneshot_base_dir = os.path.join(os.path.dirname(__file__), "instructions", "one_shot_examples")

    # Small helpers
    def _p(*parts: str) -> str:
        return os.path.join(oneshot_base_dir, *parts)

    def _read(path: str) -> str:
        with open(path, 'r', encoding='utf-8') as f:
            return f.read().strip()

    def _extract_header_and_statement(lean_text: str) -> tuple[str, str]:
        """Extract header (imports/setup) and statement (theorem/definition) from Lean text.
        
        Args:
            lean_text: The complete Lean file content as a string
            
        Returns:
            A tuple of (header, statement) where:
            - header: All content before the first theorem/definition/lemma
            - statement: The first theorem/definition/lemma found
        """
        lines = lean_text.strip().split('\n')
        
        # Find the first theorem/definition/lemma
        statement_start = -1
        for i, line in enumerate(lines):
            stripped = line.strip()
            if stripped.startswith(('theorem ', 'def ', 'lemma ', 'axiom ', 'structure ', 'class ', 'inductive ', 'instance ')):
                statement_start = i
                break
        
        if statement_start == -1:
            # No theorem/definition found, return everything as header
            return lean_text.strip(), ""
        
        # Split into header and statement
        header_lines = lines[:statement_start]
        statement_lines = lines[statement_start:]
        
        # Clean up header (remove trailing empty lines)
        while header_lines and not header_lines[-1].strip():
            header_lines.pop()
        
        # Clean up statement (remove leading empty lines)
        while statement_lines and not statement_lines[0].strip():
            statement_lines.pop(0)
        
        header = '\n'.join(header_lines).strip()
        statement = '\n'.join(statement_lines).strip()
        
        return header, statement

    for key in example_keys:
        # Load English statement
        input_text = _read(_p("clean_texts", f"{key}.txt"))

        # Load formalized statement and extract theorem signature
        # formalized_statement, header = _extract_header_and_statement(_read(_p("formalizations", f"{key}.lean")))

        # Load the formalized statement with header
        formalized_statement = _read(_p("formalizations", f"{key}.lean"))

        # Optional intermediates
        semiformalized_structure = ""
        formalized_structure = ""
        formalized_text = ""

        # Stage >= 3: semi-formalized structure
        if int(args.method[0]) >= 3:
            semi_path = _p("semiformalized_structures", f"{key}.json5")
            if os.path.exists(semi_path):
                semi_raw = _read(semi_path)
                if args.model in REASONING_MODEL_SET and (getattr(args, 'cot_for_reasoning_models', 'no') in {"no", "minimal"}):
                    semiformalized_structure = json.dumps(json5.loads(semi_raw), indent=4, ensure_ascii=False)
                else:
                    semiformalized_structure = semi_raw

        # Stage 3: formalized text from semi
        if args.method == "3_semi-formalize":
            ft_path = _p("formalized_texts_from_semi", f"{key}.txt")
            if os.path.exists(ft_path):
                ft_raw = _read(ft_path)
                if args.model in REASONING_MODEL_SET and getattr(args, 'cot_for_reasoning_models', 'no') == 'no':
                    lines = ft_raw.split('\n')
                    formalized_text = lines[-3] + "\n\n" + lines[-1] if len(lines) >= 3 else ft_raw
                else:
                    formalized_text = ft_raw

        # Stage 4: formalized structure + declarations + text-from-formal
        if args.method == "4_formalized-structure":
            fs_path = _p("formalized_structures", f"{key}.json5")
            if os.path.exists(fs_path):
                fs_raw = _read(fs_path)
                if args.model in REASONING_MODEL_SET and (getattr(args, 'cot_for_reasoning_models', 'no') in {"no", "minimal"}):
                    formalized_structure = json.dumps(json5.loads(fs_raw), indent=4, ensure_ascii=False)
                else:
                    formalized_structure = fs_raw

            ftf_path = _p("formalized_texts_from_formal", f"{key}.txt")
            if os.path.exists(ftf_path):
                ftf_raw = _read(ftf_path)
                if args.model in REASONING_MODEL_SET and getattr(args, 'cot_for_reasoning_models', 'no') == 'no':
                    lines = ftf_raw.split('\n')
                    formalized_text = lines[-3] + "\n\n" + lines[-1] if len(lines) >= 3 else ftf_raw
                else:
                    formalized_text = ftf_raw

        # Compose example messages
        user_input = f"English Statement:\n\n{input_text}"
        example_messages[0]["content"].append({"type": "input_text", "text": user_input})

        if args.method in {"1_direct", "2_self-refine"}:
            assistant_output = f"Formalized Statement:\n\n<<< {formalized_statement} >>>\n\n"
        elif args.method == "3_semi-formalize":
            assert semiformalized_structure != "", "Semi-formalized structure should not be empty!"
            assistant_output = (
                f"Semi-Formalized Structure:\n\n{semiformalized_structure}\n\n\n"
                f"Formalized Statement:\n\n{formalized_text}\n\n"
            )
        elif args.method == "4_formalized-structure":
            assert formalized_structure != "", "Formalized structure should not be empty!"
            assistant_output = (
                f"Semi-Formalized Structure:\n\n{semiformalized_structure}\n\n\n"
                f"Formalized Structure:\n\n{formalized_structure}\n\n\n"
                f"Formalized Statement:\n\n{formalized_text}\n\n"
            )
        else:
            raise NotImplementedError(f"Unsupported method: {args.method}")

        example_content.append({"type": "input_text", "text": f"{user_input}\n\n\n{assistant_output}"})
        example_messages.append({"role": "assistant", "content": [{"type": "output_text", "text": assistant_output}]})

    return example_content, example_messages


async def process_with_semaphore(task: Awaitable[bool], semaphore: asyncio.Semaphore) -> bool:
    async with semaphore:
        return await task


def merge_usage_dicts(accumulated: dict[str, Any], new_usage: dict[str, Any]) -> dict[str, Any]:
    """Recursively merge usage dictionaries.

    Rules:
    - If both values are dicts: merge recursively.
    - If both values are numeric (int/float): sum them (handles keys like tokens, cost).
    - If key not present: copy as-is.
    - Otherwise: prefer existing type and keep the original value (no error).
    """

    for key, value in new_usage.items():
        if key not in accumulated:
            accumulated[key] = value
            continue

        cur = accumulated[key]
        # Merge nested dictionaries
        if isinstance(value, dict) and isinstance(cur, dict):
            accumulated[key] = merge_usage_dicts(cur, value)
            continue

        # Sum numeric fields (supports int/float)
        if isinstance(value, (int, float)) and isinstance(cur, (int, float)):
            accumulated[key] = cur + value
            continue

        # If types differ or are non-mergeable, keep the existing value to avoid crashes
        # (e.g., provider may include strings/None); do not raise.
        # Optionally, you could log/debug here if needed.

    return accumulated


async def autoformalize_single_instance(
    category: str,
    run_idx: int,
    instance_idx: int,
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    pred_dir: Optional[str],
    validator: Any,  # Validator instance (type depends on dataset)
    llm: UnifiedModel,
    client: Any,
    args: argparse.Namespace,
    # For ProofNet Part
    sample: Dict = None
) -> Dict:
    """Process a single instance asynchronously"""

    _log_info(args, "------------------------------------------------------------")
    _log_info(args, f"Processing instance {instance_idx} in category {category} and run {run_idx} with: {llm.model_id}")
    _log_info(args, f"Inference Args: {llm.get_config()}")
    _log_info(args, "------------------------------------------------------------")

    # Create detailed logs directory structure for this instance
    detailed_logs_base = getattr(args, 'detailed_logs_dir', None)
    instance_detailed_dir = None
    if detailed_logs_base:
        # Create problem-specific directory using sample information if available
        # Use the same logic as in checker to ensure consistency
        if sample:
            problem_id = sample.get("problem_id", sample.get("name", f"problem_{instance_idx}"))
        else:
            problem_id = f"problem_{instance_idx}"
        
        instance_detailed_dir = os.path.join(detailed_logs_base, f"run_{run_idx}", problem_id)
        queries_dir = os.path.join(instance_detailed_dir, "queries")
        os.makedirs(queries_dir, exist_ok=True)
        
        # Save problem info
        problem_info = {
            "problem_id": problem_id,
            "instance_idx": instance_idx,
            "category": category,
            "run_idx": run_idx,
            "model": llm.model_id,
            "dataset": getattr(args, 'dataset', 'unknown'),
            "method": getattr(args, 'method', 'unknown'),
            "timestamp": __import__('datetime').datetime.now().isoformat()
        }
        if sample:
            problem_info.update({
                "informal_statement": sample.get('informal_stmt', ''),
                "formal_statement_ground_truth": sample.get('formal_stmt', ''),
                "source": sample.get('source', ''),
                "problem_name": sample.get('problem_name', '')
            })
        
        try:
            with open(os.path.join(instance_detailed_dir, "problem_info.json"), "w", encoding="utf-8") as f:
                json.dump(problem_info, f, indent=2)
        except Exception:
            pass  # Don't fail pipeline due to logging issues

    # Load the problem text for user input
    problem_text = sample.get('informal_stmt', '')
    # header = sample.get('header_wo_helper', '')

    # Prepare user_content for ProofNet
    user_content = [{"type": "input_text", "text": "Here is your problem:\n\n"}]

    user_content.append(
        {
            "type": "input_text",
            "text": (
                f"English Statement:\n\n{problem_text}\n\n\n"
                "Now please formalize the English Statement strictly adhering to the guidelines and examples provided above.\n\n"
            ),
        }
    )
    _log_info(args, "✅ Test: Loading ProofNet data")


    # Construct messages
    messages: Messages = []
    messages.append({"role": "developer", "content": system_content})

    # Only add the example messages if `num_examples` > 0
    if args.num_examples == 0:
        # Add only user content
        messages.append({"role": "user", "content": user_content})
    else:
        # Choose the example format
        if args.example_format == "content":
            example_messages = [{"role": "user", "content": example_content + user_content}]
        # Add the static examples to the messages
        messages.extend(example_messages)


    # If method is direct, then there's no need to self-refine, so we set num_query to 1
    num_query = args.num_query
    if args.method == "1_direct" and args.num_query > 1:
        _log_warning(args, f"⚠️  Method is direct, setting num_query from {args.num_query} to 1!")
        num_query = 1

    # Save the accumulated token usage from all queries
    usage_list: list[dict[str, Any]] = []
    accumulated_usage: dict[str, Any] = {}

    for query_idx in range(num_query):
        # Message format will be converted internally in the UnifiedModel
        response_text, usage, reasoning_summary_list, _ = await llm.get_response_async(client, messages)

        # Save the token usage
        usage_list.append(usage)
        # Accumulate the token usage
        accumulated_usage = merge_usage_dicts(accumulated_usage, usage)

        # Save detailed response info to detailed_logs (merged from model_responses)
        if instance_detailed_dir:
            query_dir = os.path.join(instance_detailed_dir, "queries", f"query_{query_idx}")
            os.makedirs(query_dir, exist_ok=True)  # Ensure query_dir exists

            # Save complete model response as a separate file in detailed_logs
            full_response_file = os.path.join(query_dir, "full_response.txt")
            with open(full_response_file, "w", encoding="utf-8") as f:
                f.write("=" * 60 + "\n")
                # save all the arguments
                f.write(f"Arguments:\n\n{str(args)}\n\n")
                f.write("=" * 60 + "\n")
                # save the English statement
                f.write(f"English Statement:\n\n{problem_text}\n\n")
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


            # Update response.json with full response content
            response_info = {
                "query_index": query_idx,
                "model_response": response_text,  # Save full response instead of just extracted content
                "usage": usage,
                "response_time_ms": None,
                "reasoning_summary": reasoning_summary_list,
                "timestamp": __import__('datetime').datetime.now().isoformat()
            }
            with open(os.path.join(query_dir, "response.json"), "w", encoding="utf-8") as f:
                json.dump(response_info, f, indent=2)

        # Add the assistant response to the context
        messages.append({"role": "assistant", "content": [{"type": "output_text", "text": response_text}]})

        # Also make the prediction directory if it doesn't exist
        if pred_dir:
            os.makedirs(pred_dir, exist_ok=True)

        # Initialize variables
        model_prediction = ""
        error_message = ""

        # Validate the model prediction
        pattern = r"<<<(.*?)>>>"
        matches = re.findall(pattern, response_text, re.DOTALL)
        if matches:
            # Use the content within <<< >>>
            model_prediction = matches[-1]
            model_prediction = re.sub(r"\s+", " ", model_prediction).strip()
        else:
            # If no <<< >>> found, try to extract Lean snippet from the response
            # Start by locating the last occurrence of the Mathlib import header
            last_import_idx = response_text.rfind('import Mathlib')

            if last_import_idx != -1:
                # Grab everything starting from the header up to (and including) the next sorry
                sorry_idx = response_text.find('sorry', last_import_idx)
                if sorry_idx != -1:
                    snippet_end = sorry_idx + len('sorry')
                    model_prediction = response_text[last_import_idx:snippet_end].strip()
                else:
                    model_prediction = response_text[last_import_idx:].strip()
            else:
                model_prediction = response_text.strip()

        # Persist the raw predicted statement to statements/generation for this run/instance
        try:
            if pred_dir:
                os.makedirs(pred_dir, exist_ok=True)
                with open(os.path.join(pred_dir, f"{instance_idx}.lean"), "w", encoding="utf-8") as _pf:
                    _pf.write(model_prediction if model_prediction else "")
        except Exception:
            # Do not fail pipeline due to logging issues
            pass

        if not args.quiet:
            logger.info("=" * 60)
            logger.info(f"Current Query: {query_idx + 1}")
            logger.info(f"Instance {instance_idx} pred: {model_prediction}")
            logger.info("-" * 60)

        # Since the model generated the header, no need to pass the header to validator
        error_message = validator.validate(model_prediction, str(instance_idx), header="")

        print("====================================================")
        print(f"attempt {query_idx + 1}, error_message: {error_message}")
        print("====================================================")

        if not args.quiet:
            logger.info(f"Instance {instance_idx} error_message: {error_message}")
            logger.info("-" * 60)

        # Save detailed query logs
        if instance_detailed_dir:
            query_dir = os.path.join(instance_detailed_dir, "queries", f"query_{query_idx}")
            os.makedirs(query_dir, exist_ok=True)
            
            # Save request info
            # Reconstruct the exact messages sent to the model for this query
            # (exclude the assistant response we just appended above if present)
            try:
                if messages and messages[-1].get("role") == "assistant":
                    request_messages = messages[:-1]
                else:
                    request_messages = messages
            except Exception:
                request_messages = messages

            request_info = {
                "query_index": query_idx,
                "problem_id": problem_info.get('problem_id', f"problem_{instance_idx}"),
                "system_prompt": system_content,
                "user_prompt": messages[-2]['content'] if len(messages) >= 2 else [],  # Last user message
                # Include full messages so logs capture one-shot examples as sent
                "messages": request_messages,
                "model": llm.model_id,
                "temperature": getattr(args, 'temperature', None),
                "timestamp": __import__('datetime').datetime.now().isoformat()
            }

            # Also save the messages separately for easier inspection
            try:
                with open(os.path.join(query_dir, "request_messages.json"), "w", encoding="utf-8") as f:
                    json.dump(request_messages, f, indent=2)
            except Exception:
                pass
            
            # Save response info
            response_info = {
                "query_index": query_idx,
                "model_response": response_text,
                "usage": usage,
                "response_time_ms": None,  # Could be added if timing info is available
                "reasoning_summary": reasoning_summary_list,
                "timestamp": __import__('datetime').datetime.now().isoformat()
            }
            
            # Save validation result
            validation_result = {
                "query_index": query_idx,
                "validation_status": "success" if (error_message == "" or error_message is None) else "failed",
                "is_syntactically_valid": error_message == "" or error_message is None,
                "typecheck_success": error_message == "" or error_message is None,
                "validation_time_ms": None,  # Could be added if timing info is available
                "validator_version": getattr(validator, 'version', 'unknown'),
                "timestamp": __import__('datetime').datetime.now().isoformat()
            }
            
            # Save error details
            error_details = {
                "query_index": query_idx,
                "lean_code_lines": len(model_prediction.split('\n')) if model_prediction else 0,
                "errors": [],
                "warnings": [],
                "lean_environment_info": {
                    "header": "",
                    "dataset": getattr(args, 'dataset', 'unknown')
                }
            }
            
            if error_message and error_message.strip():
                # Parse error message for detailed error info
                error_details["errors"].append({
                    "line": None,
                    "column": None,
                    "severity": "error",
                    "error_type": "validation_error",
                    "message": error_message,
                    "context": "validation failed",
                    "suggestion": None
                })

            # Save all files
            try:
                with open(os.path.join(query_dir, "request.json"), "w", encoding="utf-8") as f:
                    json.dump(request_info, f, indent=2)
                with open(os.path.join(query_dir, "response.json"), "w", encoding="utf-8") as f:
                    json.dump(response_info, f, indent=2)
                with open(os.path.join(query_dir, "extracted_lean.lean"), "w", encoding="utf-8") as f:
                    f.write(model_prediction if model_prediction else "")
                with open(os.path.join(query_dir, "validation_result.json"), "w", encoding="utf-8") as f:
                    json.dump(validation_result, f, indent=2)
                with open(os.path.join(query_dir, "error_details.json"), "w", encoding="utf-8") as f:
                    json.dump(error_details, f, indent=2)
            except Exception:
                pass  # Don't fail pipeline due to logging issues

        # if no error message, we just return the result and exit the query loop
        if error_message == "" or error_message is None:
            if not args.quiet:
                logger.info(f"Instance {instance_idx} succeeded after {query_idx + 1} queries")
                logger.info("=" * 60)

            # Save final query result for successful case
            if instance_detailed_dir:
                final_query_result = {
                    "problem_id": problem_info.get('problem_id', f"problem_{instance_idx}"),
                    "total_queries": query_idx + 1,
                    "selected_query": {
                        "query_index": query_idx,
                        "reason": "validation_success",
                        "validation_status": "success"
                    },
                    "all_query_summary": [
                        {
                            "query_index": i,
                            "validation_status": "success" if i == query_idx else "failed",
                            "error_count": 0 if i == query_idx else 1
                        }
                        for i in range(query_idx + 1)
                    ],
                    "final_lean_code": model_prediction,
                    "selection_timestamp": __import__('datetime').datetime.now().isoformat()
                }
                try:
                    with open(os.path.join(instance_detailed_dir, "queries", "final_query_result.json"), "w", encoding="utf-8") as f:
                        json.dump(final_query_result, f, indent=2)
                except Exception:
                    pass

            return {
                "formal_stmt_pred": model_prediction,
                "typecheck_result": {
                    "is_success": True,
                    "error_message": None,
                    "num_queries": query_idx + 1
                },
                "category": category,
                "run_idx": run_idx,
                "instance_idx": instance_idx,
                "model": llm.model_id,
                "accumulated_usage": accumulated_usage,
                "reasoning_summary": reasoning_summary_list,
            }
        # Build error-aware feedback (uses validator artifacts if available)
        feedback = _build_error_aware_feedback(
            dataset=args.dataset,
            validator=validator,
            instance_idx=instance_idx,
            raw_error=error_message or "",
        )
        messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})

    if not args.quiet:
        logger.info(f"Instance {instance_idx} failed after {num_query} attempts")
        logger.info("=" * 60)
    
    # Save final query result for failed case
    if instance_detailed_dir:
        final_query_result = {
            "problem_id": problem_info.get('problem_id', f"problem_{instance_idx}"),
            "total_queries": num_query,
            "selected_query": {
                "query_index": num_query - 1,
                "reason": "max_attempts_reached",
                "validation_status": "failed"
            },
            "all_query_summary": [
                {
                    "query_index": i,
                    "validation_status": "failed",
                    "error_count": 1
                }
                for i in range(num_query)
            ],
            "final_lean_code": model_prediction,
            "selection_timestamp": __import__('datetime').datetime.now().isoformat()
        }
        try:
            with open(os.path.join(instance_detailed_dir, "queries", "final_query_result.json"), "w", encoding="utf-8") as f:
                json.dump(final_query_result, f, indent=2)
        except Exception:
            pass
    
    return {
        "formal_stmt_pred": model_prediction,
        "typecheck_result": {
            "is_success": False,
            "error_message": error_message if error_message else "Max attempts reached",
            "num_queries": num_query
        },
        "category": category,
        "run_idx": run_idx,
        "instance_idx": instance_idx,
        "model": llm.model_id,
        "accumulated_usage": accumulated_usage,
        "reasoning_summary": reasoning_summary_list,
    }


async def autoformalize_batch_instances_vanilla(
    task_list: list[tuple[str, int, int, Optional[str], Any]],  # Any is validator instance
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    llm: UnifiedModel,
    client: Any,
    args: argparse.Namespace
) -> list[Dict]:
    # Process all instances at once
    result_list: list[Dict] = []

    # Calculate number of instances to process
    if args.dataset == "DSL":
        num_instances = len(args.dsl_samples)
    elif args.dataset == "ProofNet":
        num_instances = len(args.proofnet_samples)
    else:
        num_instances = len(args.testing_idx)

    _log_info(args, f"🚀 Starting async processing of {num_instances} instances with max {args.num_async} concurrent tasks ...")

    # Create tasks for all instances
    async_task_list = []

    for task in task_list:
        category, run_idx, instance_idx, pred_dir, validator = task
        sample = None
        if args.dataset == "DSL" and hasattr(args, 'dsl_data') and args.dsl_data and instance_idx < len(args.dsl_data):
            sample = args.dsl_data[instance_idx]
        elif hasattr(args, 'proofnet_data') and args.proofnet_data and instance_idx < len(args.proofnet_data):
            sample = args.proofnet_data[instance_idx]
        async_task = autoformalize_single_instance(
            category, run_idx, instance_idx, system_content, example_content, example_messages, pred_dir, validator, llm, client, args, sample
        )
        async_task_list.append(async_task)

    # Process tasks with concurrency limit
    semaphore = asyncio.Semaphore(args.num_async)
    coros = [process_with_semaphore(t, semaphore) for t in async_task_list]
    futures = [asyncio.create_task(coro) for coro in coros]

    # Choose `asyncio.as_completed` over `asyncio.gather` to stream the results
    # we don't need to keep the original order in the task list
    # since `process_single_instance` will save our results to files with ordered names
    # Set progress description based on dataset type
    if args.dataset == "ProofNet":
        progress_desc = f"Dataset {args.dataset}"
    else:
        progress_desc = f"Category {args.category}"

    for future in async_tqdm.as_completed(
        futures, total=len(task_list), desc=progress_desc, unit="instance", position=0, leave=True, ncols=100, dynamic_ncols=True
    ):
        result = await future
        result_list.append(result)

    return result_list


async def autoformalize_batch_instances_caching(
    task_list: list[tuple[str, int, int, str, Any]],  # Any is validator instance
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    llm: UnifiedModel,
    client: Any,
    args: argparse.Namespace
) -> list[Dict]:
    # Process the first instance individually to enable prompt caching
    result_list: list[Dict] = []

    _log_info(args, f"🚀 Processing first instance in category {task_list[0][0]} and run {task_list[0][1]} to enable prompt caching...")
    # Fetch the first instance's information
    first_category, first_run_idx, first_instance_idx, pred_dir, validator = task_list[0]
    # Get the first instance's formalization
    first_sample = None
    if args.dataset == "DSL" and hasattr(args, 'dsl_data') and args.dsl_data and first_instance_idx < len(args.dsl_data):
        first_sample = args.dsl_data[first_instance_idx]
    elif hasattr(args, 'proofnet_data') and args.proofnet_data and first_instance_idx < len(args.proofnet_data):
        first_sample = args.proofnet_data[first_instance_idx]
    first_result = await autoformalize_single_instance(
        first_category, first_run_idx, first_instance_idx, system_content, example_content, example_messages, pred_dir, validator, llm, client, args, first_sample
    )
    result_list.append(first_result)

    # Process the rest of the instances using the vanilla function
    if len(task_list) > 1:
        remaining_results = await autoformalize_batch_instances_vanilla(task_list[1:], system_content, example_content, example_messages, llm, client, args)
        result_list.extend(remaining_results)

    return result_list          


async def autoformalize_batch_instances(
    task_list: list[tuple[str, int, int, Optional[str], Optional[str], Any]],  # Any is validator instance
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    llm: UnifiedModel,
    args: argparse.Namespace
) -> list[Dict]:
    # Determine which function to call based on caching preference
    target_function = autoformalize_batch_instances_caching if args.enable_caching else autoformalize_batch_instances_vanilla

    # Initialize the client if needed
    model_id = llm.model_id
    if model_id in (BEDROCK_CLAUDE_MODEL_LIST + BEDROCK_CLAUDE_THINKING_MODEL_LIST):
        async with llm.async_session.client(**llm.client_args) as client:
            return await target_function(task_list, system_content, example_content, example_messages, llm, client, args)
    else:
        client = None
        return await target_function(task_list, system_content, example_content, example_messages, llm, client, args)


def autoformalize_batch_instances_sync(
    task_list: list[tuple[str, int, int, Optional[str], Optional[str], Any]],  # Any is validator instance
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    llm: UnifiedModel,
    args: argparse.Namespace
) -> list[Dict]:
    """Synchronous wrapper for async autoformalize_batch_instances"""
    return asyncio.run(autoformalize_batch_instances(task_list, system_content, example_content, example_messages, llm, args))


async def debug_single_instance(
    category: str,
    instance_idx: int,
    system_content: Content,
    example_content: Content,
    example_messages: Messages,
    pred_dir: str,
    validator: Any,  # Validator instance (type depends on dataset)
    llm: UnifiedModel,
    args: argparse.Namespace,
    # The following is used for ProofNet Part
    sample: Dict = None
) -> None:
    """Debug mode for single instance processing"""
    _log_info(args, "=" * 80)
    _log_info(args, f"🔧 DEBUG MODE: Processing instance {instance_idx} in category {category}")
    _log_info(args, "=" * 80)

    # Use run_idx = 1 for debug mode
    run_idx = 1

    try:
        result = await autoformalize_single_instance(
            category, run_idx, instance_idx, system_content, example_content, example_messages,
            pred_dir, validator, llm, None, args, sample
        )

        _log_info(args, "=" * 80)
        if result:
            _log_info(args, "✅ Debug instance completed successfully!")
        else:
            _log_info(args, "❌ Debug instance failed!")
        _log_info(args, "=" * 80)

    except Exception as e:
        _log_info(args, "=" * 80)
        _log_error(args, f"❌ Debug instance error: {e}")
        if not getattr(args, 'quiet', False):
            import traceback
            traceback.print_exc()
        _log_info(args, "=" * 80)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--dataset",
        type=str,
        choices=["ProofNet", "connf", "DSL"],
        required=False,
        default=None,
        help="Testing dataset",
    )
    parser.add_argument(
        "--experiment_type",
        type=str,
        choices=["barebone", "oracle", "learned"],
        required=False,
        default="barebone",
        help="DSL experiment type (only used when dataset is DSL)",
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
        ],
        required=False,
        help="Testing category",
        default="",
    )
    parser.add_argument(
        "--method",
        type=str,
        choices=["1_direct", "2_self-refine", "3_semi-formalize", "4_formalized-structure", "5_implicit-inference", "6_self-refine_semantic"],
        required=False,
        default=None,
        help="Method to use for autoformalization",
    )
    parser.add_argument(
        "--model",
        type=str,
        required=False,
        default=None,
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
        required=False,
        default=None,
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
    parser.add_argument("--num_run", type=int, default=5, help="Number of independent runs (each run processes all samples)")
    parser.add_argument("--root_dir", type=str, default=ROOT_DIR, help="Root directory")
    parser.add_argument("--result_dir_name", type=str, default="result", help="Name of the result directory")
    parser.add_argument("--dataset_root", type=str, default=None, help="Optional dataset root override; else env DATASET_ROOT; else <root_dir>/data")
    parser.add_argument("--debug_instance", type=int, default=None, help="Debug specific instance (for development)")
    parser.add_argument("--launch_debug", action="store_true", help="Launch debug mode for single instance")
    parser.add_argument("--save_detailed_response", action="store_true", help="Save detailed response files (large files, disable for production)")
    parser.add_argument("--limit", type=int, default=0, help="Limit number of samples to process per run (0 means all available samples)")
    parser.add_argument(
        "--relations_file",
        type=str,
        default="Relations_barebone",
        help="Name of the relations file under the directory, for simplification of the model prediction",
    )
    parser.add_argument(
        "--dsl_doc",
        type=str,
        default="doc_barebone.txt",
        help="Name of the DSL documentation file under the directory",
    )
    parser.add_argument(
        "--config",
        type=str,
        help="Path to JSON/JSON5 config file to load parameters from",
    )
    parser.add_argument(
        "--quiet",
        dest="quiet",
        action="store_true",
        help="Silence validator logs and rely on progress bars",
    )
    parser.add_argument(
        "--no-quiet",
        dest="quiet",
        action="store_false",
        help="Enable validator log output",
    )
    parser.set_defaults(quiet=True)

    args = parser.parse_args()

    # Load config file if provided (CLI has precedence)
    args = load_config_into_args(args, parser)

    # Configure shared quiet settings and logging sinks
    args.quiet = bool(getattr(args, 'quiet', True))
    configure_logging(args.quiet)
    args.validator_quiet = bool(args.quiet)

    if getattr(args, 'dataset', None) == "DSL":
        args.dsl_relations_path = _resolve_dsl_relations_path(args)
    else:
        args.dsl_relations_path = ""

    # Checker-only mode removed; checker is decoupled and should be run separately

    # Validate critical fields after config merge
    for required_key in ["dataset", "method", "model", "reasoning"]:
        if getattr(args, required_key) in (None, ""):
            raise ValueError(f"Missing required parameter '{required_key}'. Provide it via --{required_key} or in --config")

    # The argument `num_examples` must be non-negative
    if args.num_examples < 0:
        raise ValueError(f"`num_examples` must be non-negative, but got {args.num_examples}")

    # The arguments `example_choices` must be consistent with `num_examples`
    first_choice = args.example_choices[0]
    if (first_choice == "none" and args.num_examples != 0) or (
        first_choice != "none" and first_choice != "dynamic" and len(args.example_choices) != args.num_examples
    ):
        raise ValueError(f"`example_choices` must be consistent with `num_examples`, but got {args.example_choices} and {args.num_examples}")


    # Add additional arguments
    if args.dataset == "ProofNet":
        # For ProofNet, load data directly and handle samples by their indices
        # Note: ProofNet doesn't use categories - each sample is processed independently
        # The limit parameter controls how many samples to process (applied once at loading)
        # The num_run parameter controls how many times to run the entire set of samples
        # use top-level json import; avoid function-scoped import to prevent shadowing
        # Resolve dataset root robustly
        data_root = (
            args.dataset_root
            or os.environ.get("DATASET_ROOT")
            or os.path.join(args.root_dir, "data")
            or os.path.join(ROOT_DIR, "data")
        )
        benchmark_file = os.path.join(data_root, "proofnet", "benchmark.jsonl")
        with open(benchmark_file, 'r', encoding='utf-8') as f:
            proofnet_data = [json.loads(line) for line in f]

        # Apply limit if specified (limit the total number of samples to process)
        if args.limit > 0:
            proofnet_data = proofnet_data[:args.limit]
            _log_info(args, f"📊 Limited to first {args.limit} ProofNet samples (each run will process these {args.limit} samples)")

        # Store the data and create sample identifiers
        args.proofnet_data = proofnet_data
        args.proofnet_samples = list(range(len(proofnet_data)))  # Use indices as sample identifiers
        _log_info(args, f"✅ Loaded {len(proofnet_data)} ProofNet samples for {args.num_run} independent run(s)")

        library_file = os.path.join(data_root, "proofnet", "library.jsonl")
        with open(library_file, 'r', encoding='utf-8') as f:
            premises_with_informalization = [json.loads(line) for line in f]
        args.premises_dict = {p['full_name']: p for p in premises_with_informalization}
        _log_info(args, f"✅ Loaded {len(proofnet_data)} ProofNet samples and {len(premises_with_informalization)} premises")

    elif args.dataset == "DSL":
        # For DSL experiments, load data based on experiment type
        data_root = (
            args.dataset_root
            or os.environ.get("DATASET_ROOT")
            or os.path.join(args.root_dir, "data")
            or os.path.join(ROOT_DIR, "data")
        )

        # if args.experiment_type == "barebone":
        #     dsl_data_file = os.path.join(data_root, "ProofNet-Lean4_proof_hard.csv")
        # else:  # oracle or learned
        dsl_data_file = os.path.join(data_root, "ProofNet-Lean4_proof_hard.csv")

        # Load DSL data from CSV
        import csv
        dsl_data = []
        with open(dsl_data_file, 'r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                dsl_data.append(row)

        # Apply limit if specified
        if args.limit > 0:
            dsl_data = dsl_data[:args.limit]
            _log_info(args, f"📊 Limited to first {args.limit} DSL samples (each run will process these {args.limit} samples)")

        # Store the data and create sample identifiers
        args.dsl_data = dsl_data
        args.dsl_samples = list(range(len(dsl_data)))  # Use indices as sample identifiers
        _log_info(args, f"✅ Loaded {len(dsl_data)} DSL samples ({args.experiment_type} experiment) for {args.num_run} independent run(s)")

        # # Load premises (reuse ProofNet premises for DSL)
        # library_file = os.path.join(data_root, "proofnet_dsl", "library.jsonl")
        # with open(library_file, 'r', encoding='utf-8') as f:
        #     premises_with_informalization = [json.loads(line) for line in f]
        # args.premises_dict = {p['full_name']: p for p in premises_with_informalization}
        # _log_info(args, f"✅ Loaded {len(premises_with_informalization)} premises for DSL experiment")

   
    # Construct instruction
    system_content = construct_instruction(args)
    # Construct static in-context examples, if `num_examples` > 0 and `example_choices` is not "dynamic"
    example_content: Content = []
    example_messages: Messages = []
    if args.num_examples > 0 and first_choice != "dynamic":
        example_content, example_messages = construct_example_messages(args.dataset, args.num_examples, args.example_choices, args, True)

    # Initialize result dictionary for incremental saving
    import collections as C
    autoformalization_result: Dict[str, List[Dict]] = C.defaultdict(list)

    # New output structure: <root_dir>/<result_dir_name>/<model>_<method>[_<exp>]_<shot>/{files}
    safe_model = str(args.model).replace('/', '_') if getattr(args, 'model', None) else 'model'
    method_name = str(args.method) if getattr(args, 'method', None) else 'method'
    
    # Determine shot type based on num_examples
    shot_type = "1" if getattr(args, 'num_examples', 0) > 0 else "0"
    
    run_folder_name = f"{safe_model}_{method_name}"
    # For DSL experiments, append experiment type (e.g., barebone/oracle/learned)
    if getattr(args, 'dataset', None) == 'DSL' and getattr(args, 'experiment_type', None):
        run_folder_name = f"{run_folder_name}_{args.experiment_type}"
    
    # Add shot type to folder name
    run_folder_name = f"{run_folder_name}_{shot_type}"

    base_output_dir = os.path.join(args.root_dir, args.result_dir_name)
    run_dir = os.path.join(base_output_dir, run_folder_name)
    
    # New structure: result files directly in run_dir, detailed logs in detailed_logs/
    detailed_logs_dir = os.path.join(run_dir, "detailed_logs")
    
    # Set detailed_logs_dir in args for access in autoformalize_single_instance
    args.detailed_logs_dir = detailed_logs_dir
    
    # No longer need separate directories for responses and candidates
    # Everything is now saved in detailed_logs

    # Keep formal_candidates_root_dir for compatibility
    formal_candidates_root_dir = os.path.join(run_dir, "candidates")

    # Define save path for incremental results with requested naming (directly in run_dir)
    result_save_path = os.path.join(run_dir, f"{run_folder_name}_result.json")

    # Load existing results if file exists
    if os.path.exists(result_save_path) and os.path.isfile(result_save_path):
        _log_info(args, f"🔄 Loading existing autoformalization results from {result_save_path}...")
        try:
            with open(result_save_path, "r", encoding="utf-8") as f:
                loaded_results = json.load(f)
                for k, v in loaded_results.items():
                    autoformalization_result[k] = v
            _log_info(args, f"✅ Loaded {len(autoformalization_result)} existing results")
        except Exception as e:
            _log_warning(args, f"⚠️ Failed to load existing results: {e}, starting fresh...")
    else:
        _log_info(args, "📝 Starting fresh autoformalization run...")

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
            base_url = "http://localhost:8000/v1",
            max_tokens=1024,
            temperature=args.temperature
        )
    else:
        raise ValueError(f"Invalid model: {args.model}")

    # Create minimal required directories for this run
    _log_info(args, "📂 Creating output directories")
    os.makedirs(run_dir, exist_ok=True)
    # Do NOT pre-create responses/candidates to avoid empty artifacts
    _log_info(args, f"✅ Created run directory: {run_dir}")

    # track total successful and failed instances
    total_successful = 0
    total_failed = 0

    # Handle debug mode
    if args.launch_debug:
        if args.debug_instance is None:
            _log_error(args, "❌ Debug mode requires --debug_instance to be specified")
            return

        _log_info(args, "🔧 Launching debug mode for single instance...")
        if args.dataset == "ProofNet":
            category = "ProofNet"
        else:
            category = args.category[0] if args.category else "Debug"
        instance_idx = args.debug_instance

        # Create directories for debug (no longer needed since we save to detailed_logs)
        pass

        # Create validator for debug
        ValidatorClass = get_validator_class(args.dataset)
        relations_arg = _relations_path_for_dataset(args, args.dataset)
        validator = instantiate_validator(
            ValidatorClass,
            root_dir=args.root_dir,
            tmp_dir=os.path.join(run_dir, "tmp"),  # Use a tmp directory for validator
            relations_file=relations_arg,
            quiet=args.validator_quiet,
        )

        # Run debug instance
        sample = None
        if args.dataset == "DSL" and hasattr(args, 'dsl_data') and args.dsl_data and instance_idx < len(args.dsl_data):
            sample = args.dsl_data[instance_idx]
        elif hasattr(args, 'proofnet_data') and args.proofnet_data and instance_idx < len(args.proofnet_data):
            sample = args.proofnet_data[instance_idx]
        asyncio.run(debug_single_instance(
            category, instance_idx, system_content, example_content, example_messages,
            None, validator, llm, args, sample
        ))

        # Checker is decoupled; run it separately if desired during debug
        return
    
    # Create task list - handle different datasets appropriately
    task_list: list[tuple[str, int, int, str, str, Any]] = []  # Any is validator instance

    if args.dataset == "DSL":
        # For DSL: Direct sample processing (similar to ProofNet)
        # - Each run processes all samples in args.dsl_samples
        # - Total tasks = len(dsl_samples) * num_run
        for run_idx in range(1, args.num_run + 1):
            # Create directories for this run
            pred_dir = os.path.join(formal_candidates_root_dir, f"run_{run_idx}")
            tmp_dir = os.path.join(run_dir, "tmp", f"run_{run_idx}")

            # Ensure directories exist
            os.makedirs(pred_dir, exist_ok=True)
            os.makedirs(tmp_dir, exist_ok=True)

            # Create validator for this run
            ValidatorClass = get_validator_class(args.dataset)
            relations_arg = _relations_path_for_dataset(args, "DSL")
            validator = instantiate_validator(
                ValidatorClass,
                root_dir=args.root_dir,
                tmp_dir=tmp_dir,  # Use tmp_dir for validator
                relations_file=relations_arg,
                quiet=args.validator_quiet,
            )

            # Create tasks for each DSL sample in this run
            # Use sample index directly as instance_idx
            for sample_idx in args.dsl_samples:
                task_list.append(("DSL", run_idx, sample_idx, pred_dir, validator))

    elif args.dataset == "ProofNet":
        # For ProofNet: Direct sample processing (no category grouping)
        # - Each run processes all samples in args.proofnet_samples
        # - Total tasks = len(proofnet_samples) * num_run
        # - No category subdirectories are created
        for run_idx in range(1, args.num_run + 1):
            # Create directories for this run
            pred_dir = os.path.join(formal_candidates_root_dir, f"run_{run_idx}")
            tmp_dir = os.path.join(run_dir, "tmp", f"run_{run_idx}")

            # Ensure directories exist
            os.makedirs(pred_dir, exist_ok=True)
            os.makedirs(tmp_dir, exist_ok=True)

            # Create validator for this run
            ValidatorClass = get_validator_class(args.dataset)
            relations_arg = _relations_path_for_dataset(args, "ProofNet")
            validator = instantiate_validator(
                ValidatorClass,
                root_dir=args.root_dir,
                tmp_dir=tmp_dir,  # Use tmp_dir for validator
                relations_file=relations_arg,
                quiet=args.validator_quiet,
            )

            # Create tasks for each ProofNet sample in this run
            # Use sample index directly as instance_idx
            for sample_idx in args.proofnet_samples:
                task_list.append(("ProofNet", run_idx, sample_idx, pred_dir, validator))

    else:
        raise ValueError(f"Unsupported dataset: {args.dataset}. Only ProofNet, connf, and DSL are supported.")

    progress_bar = sync_tqdm(total=len(task_list), desc="Autoformalize", disable=False)
    try:
        if args.num_process <= 1:
            result_chunk_list = []
            for task in task_list:
                result_chunk_list.append(
                    autoformalize_batch_instances_sync([task], system_content, example_content, example_messages, llm, args)
                )
                progress_bar.update(1)
        else:
            parallel = Parallel(
                n_jobs=args.num_process,
                backend="loky",
                verbose=0,
                batch_size="auto",
                max_nbytes=None,  # No memory limit
                pre_dispatch="2*n_jobs",  # Pre-dispatch tasks for better performance
            )
            with _joblib_progress(progress_bar):
                result_chunk_list = parallel(
                    delayed(autoformalize_batch_instances_sync)([task], system_content, example_content, example_messages, llm, args)
                    for task in task_list
                )
    finally:
        progress_bar.close()

    # Flatten the multi-process result list
    result_list = [item for sublist in result_chunk_list for item in sublist]

    # Process results and update the autoformalization_result dictionary
    for result in result_list:
        # For ProofNet, connf, and DSL, use sample's full_name as key if sample data is available
        if args.dataset in ["ProofNet", "connf", "DSL"]:
            sample_data = None
            if args.dataset == "DSL" and hasattr(args, 'dsl_data') and args.dsl_data:
                sample_data = args.dsl_data
            elif hasattr(args, 'proofnet_data') and args.proofnet_data:
                sample_data = args.proofnet_data

            if sample_data:
                # Find the sample by instance_idx
                sample = next((s for s in sample_data if sample_data.index(s) == result['instance_idx']), None)
                if sample:
                    # Use full_name if available, otherwise construct it from source and problem_name
                    if 'full_name' in sample:
                        instance_key = sample['full_name']
                elif 'source' in sample and 'problem_name' in sample:
                    instance_key = f"{sample['source']}.{sample['problem_name']}"
                else:
                    instance_key = f"{result['category']}_run_{result['run_idx']}_instance_{result['instance_idx']}"
            else:
                instance_key = f"{result['category']}_run_{result['run_idx']}_instance_{result['instance_idx']}"
        else:
            instance_key = f"{result['category']}_run_{result['run_idx']}_instance_{result['instance_idx']}"
        autoformalization_result[instance_key].append(result)

    # Count successful and failed instances
    successful = sum(1 for result in result_list if result.get('typecheck_result', {}).get('is_success', False))
    failed = len(result_list) - successful
    total_successful += successful
    total_failed += failed

    # Display completion message based on dataset type
    if args.dataset == "ProofNet":
        dataset_info = f"Dataset {args.dataset}"
    else:
        dataset_info = f"Categories {args.category}"

    if failed > 0:
        _log_warning(args, f"❌ {dataset_info} completed! Success: {successful}, Failure: {failed}")
    elif successful > 0:
        _log_info(args, f"✅ {dataset_info} completed! Success: {successful}, Failure: {failed}")
    else:
        _log_warning(args, f"❌ {dataset_info} completed! Success: {successful}, Failure: {failed}")

    if total_failed > 0:
        _log_warning(args, f"❌ Total Successful: {total_successful}, Total Failure: {total_failed}")
    else:
        _log_info(args, f"✅ Total Successful: {total_successful}, Total Failure: {total_failed}")

    # Save the final results to JSON file
    _log_info(args, f"💾 Saving results to {result_save_path}...")
    try:
        os.makedirs(os.path.dirname(result_save_path), exist_ok=True)
        with open(result_save_path, "w", encoding="utf-8") as f:
            json.dump(dict(autoformalization_result), f, ensure_ascii=False, indent=2)
        _log_info(args, f"✅ Results saved successfully to {run_dir}!")
        _log_info(args, f"📊 Total instances processed: {len(autoformalization_result)}")
    except Exception as e:
        _log_warning(args, f"❌ Failed to save results: {e}")

    # Checker is decoupled; run it via afc.proofnet.proofnet_checker CLI as a separate step if desired.


if __name__ == "__main__":
    # Add --config to the existing CLI without changing downstream signatures
    # We need to reparse args here to inject config values before main()
    import sys as _sys
    _parser = argparse.ArgumentParser(add_help=False)
    _parser.add_argument('--config', type=str, default=None)
    # Peek config without consuming other args
    _peek, _ = _parser.parse_known_args()
    # Call the real main which parses full CLI; then apply config and rebind
    # We simulate by calling main() that performs full parse; to inject config
    # earlier would require broader refactor. Instead, we attach to args after
    # it is created in main pathways where needed.
    # For minimal change, we expose a module-level flag with config path.
    CONFIG_PATH = _peek.config
    main()
