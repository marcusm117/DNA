# License: Apache 2.0
# pylint: disable=R0912,C0302


# Standard Library Modules
import argparse
import csv
import json
import os
import re
from pathlib import Path
from typing import Any, cast

# External Modules
from tqdm import tqdm

# Internal Modules
from dna import (
    create_unified_model,
    UnifiedModel,
)
from dna.type_defs import Messages
from dna.leaneuclid import Validator


# Root path for Lean project
ROOT_DIR_LeanEuclidPlus = Path(__file__).parent.parent / "LeanEuclidPlus"
ROOT_DIR_PROOFNET = Path(__file__).parent.parent / "ProofNetHard"


# Prompts
CONCEPT_EXTRACTION_PROMPT = (
    "You are an expert in mathematics and logic with deep knowledge of all fields of mathematics. "
    "You are given some English mathematical statements and a list of previously extracted mathematical concepts. "
    "Your task is to extract ALL mathematical concepts mentioned in the current statements. {additional_specs}\n\n"
    "## Mathematical Concepts\n"
    "There are 3 types of mathematical concepts to extract:\n"
    "1. **Definitions of Mathematical Objects**: Point, Line, Integer, Real Number, Series, Group, Ring, etc.\n"
    "2. **Relations between Mathematical Objects**: 'a point being on a line', "
    "'an integer being even', 'a group being a subgroup of another group', etc.\n"
    "3. **Functions mapping Mathematical Objects to Mathematical Objects**: "
    "'the Euclidean distance function mapping two points in Euclidean space to a real number', "
    "'the Determinant function mapping a square matrix to a real number', etc.\n\n"
    "## Guidelines\n"
    "1. **Precision**: When extracting definitions, relations and functions, you MUST be as precise and detailed as possible. "
    "For example 'congruent' is not a precise mathematical relation! "
    "You MUST specify how many arguments and what type of arguments the relation or function takes "
    "like 'two integers being congruent modulo 3', 'two triangles being congruent', 'a list of line segments being congruent to each other', etc.\n\n"
    "2. **Well-Definedness**: Please **MAKE SURE** that each mathematical object, relation, and function you extract is well-defined, "
    "or has a conventionally well-accepted definition. "
    "For example, 'two lines being on oppossing sides of a point' is not well-defined because a point can't partition a plane into sides.\n\n"
    "3. **Abstractness**: The definitions, relations and functions you extract MUST be abstract "
    "i.e. not involving any particular objects, variables, names in the current statements. "
    "For example, 'line AB being parallel to line CD' is not abstract because it involves the names 'AB' and 'CD'.\n\n"
    "4. **Naming Consistency**: When naming concepts, you MUST align with the previously extracted concepts if they refer to the same thing. "
    "For example, if previous concepts contain 'two lines being parallel in euclidean space' "
    "and the current statements mention 'parallel lines in euclidean space', you should use exactly the name "
    "'two lines being parallel in euclidean space' for this concept extracted from the current statements."
    "Only add new concept names if they are truly new and not covered by previously extracted concepts.\n\n"
    "4. **Reasoning**: Please carefully analyze the all English statements sentence by sentence, "
    "identify all potential definitions, relations and functions, "
    "and double-check that they are well-defined. Provide your detailed step-by-step reasoning **BEFORE** outputing your final extraction answer.\n\n"
    "## Output Format\n"
    "You **MUST** provide your final extraction answer i.e. a list of extracted concepts within triple angle brackets and separated by semi-colons. "
    "Each concept is a short phrase containing any necessary characters except semi-colon!!!\n\n"
    "<<< concept1; concept2; ... >>>\n\n"
    "## Task Context:\n"
    "### Previously Extracted Concepts:\n\n{previous_concepts}\n\n\n\n"
    "### Current English Statements:\n\n{english_statements}\n\n"
)

CONCEPT_FILTERING_PROMPT = (
    "You are an expert in mathematics, logic, programming lanaguages, and formal verification "
    "with deep knowledge of all fields of mathematics and formalization of mathematics. "
    "You are given a list of mathematical concepts in English, "
    "and the documentation of a Domain-Specific Language (DSL) for formal mathematics. {additional_specs}\n\n"
    "I want to include and formalize some of these concepts into the current formal DSL. "
    "Your task is to filter out concepts that do NOT meet the criteria for inclusion.\n\n"
    "## Filtering Criteria\n"
    "You MUST filter out concepts that satisfy ANY of the following criteria:\n"
    "1. **Duplication of Other Concepts**: The concept is a duplication of another concept. "
    "For example, the concepts 'a point being the midpoint of a line segment' and 'a point dividing a line segment into two equal parts' "
    "are duplications because they describe the exact same mathematical relationship using different wording. "
    "Please keep the one with a clearer and more conventional wording. "
    "In this case, please keep the concept 'a point being the midpoint of a line segment' and filter out the other one.\n\n"
    "2. **Already Defined in Current DSL**: The concept has a direct corresponding formal relation/function/type "
    "already defined in the current DSL. "
    "For example, there is a concept 'two distinct points being on a line', and in the DSL there is a formal relation `distinctPointsOnLine` "
    "with the description: def distinctPointsOnLine (a b : Point) (L : Line) "
    "-- points a and b are distinct and on line L. The syntax is `distinctPointsOnLine a b L`. "
    "Then the concept 'two distinct points lies on a line' should be filtered out because it is already defined in the current DSL.\n\n"
    "## Guidelines\n"
    "1. **Conservative Filtering**: When in doubt, **KEEP** the concept. Only filter out concepts that clearly violate one of the criteria.\n\n"
    "2. **DSL Comparison**: Carefully compare each concept against the current DSL to identify redundancy or easy expressibility. "
    "Don't filter out concepts by mistake! "
    "Note that some concepts might be very similar to a formal relation/function/type "
    "in the current DSL, but are different in some subtle aspects. For example, "
    "the concept 'two points being on a line' is very similar to the formal relation `def distinctPointsOnLine (a b : Point) (L : Line)`, "
    "but the former allows the two points to be the same point, while the latter requires the two points to be distinct. "
    "For another example, the concept 'a set of points being on the same side of a line' is very similar to "
    "the formal relation `def sameSide (a b : Point) (L : Line)`, "
    "but the latter only formalizes the concept that 'two points being on the same side of a line', "
    "while the former allows the set of points to be more than two.\n\n"
    "3. **Reasoning**: Please carefully analyze concept by concept, compare them with other concepts and the current DSL to identify redundancy, "
    "determine which concepts should be FILTERED OUT (NOT KEEPING), "
    "and provide your detailed step-by-step reasoning **BEFORE** outputing your final filtering answer.\n\n"
    "## Output Format\n"
    "You **MUST** provide your final filtering decision as a list of concepts to FILTER OUT (NOT KEEPING) within "
    "triple angle brackets and separated by semi-colons. "
    "The name of the concepts you provide should be **EXACTLY THE SAME** as the name of the concepts in provided concept list!!!\n\n"
    "<<< concept1; concept2; ... >>>\n\n"
    "If there is no concept to filter out (KEEPING ALL CONCEPTS), please output an empty list: <<< >>>\n\n"
    "## Task Context:\n"
    "### **Current DSL Documentation:**\n\n{dsl_doc}\n\n\n\n"
    "### **Concepts for Filtering:**\n\n{concept_list}\n\n"
)

CDG_CONSTRUCTION_PROMPT = (
    "You are an expert in mathematics, logic, programming languages, and formal verification "
    "with deep knowledge of all fields of mathematics and formalization of mathematics. "
    "You are given a list of mathematical concepts in English, a list of previously analyzed concepts, "
    "and the documentation of a Domain-Specific Language (DSL) for formal mathematics. {additional_specs}\n\n"
    "Your task is to analyze the dependency structure of each concept and determine how they can be formalized in the DSL.\n\n"
    "## Dependency Analysis\n"
    "For each concept in the list, you need to determine:\n\n"
    "1. **Direct Expressibility**: Can this concept be directly expressed using existing formal types, relations, and functions in the current DSL? "
    "If yes, list the specific DSL elements that can express this concept.\n\n"
    "2. **Concept Dependencies**:If not directly expressible, what other mathematical concepts "
    "(with no direct correspondents in the current DSL) does this concept depend on? "
    "List all the prerequisite concepts needed to define this concept. "
    "These dependencies should be abstract mathematical concepts, not specific instances.\n\n"
    "3. **Formalization Status**: Based on the analysis, classify the concept as:\n"
    "   - `directly_expressible`: Can be directly expressed using existing DSL elements\n"
    "   - `needs_dependencies`: Requires other concepts to be defined first, but ultimately formalizable\n"
    "   - `impossible`: Cannot be expressed in the current DSL and would require fundamental DSL extensions\n\n"
    "## Mathematical Concepts\n"
    "There are 3 types of mathematical concepts you can add as additional dependencies:\n"
    "1. **Definitions of Mathematical Objects**: Point, Line, Integer, Real Number, Series, Group, Ring, etc.\n"
    "2. **Relations between Mathematical Objects**: 'a point being on a line', "
    "'an integer being even', 'a group being a subgroup of another group', etc.\n"
    "3. **Functions mapping Mathematical Objects to Mathematical Objects**: "
    "'the Euclidean distance function mapping two points in Euclidean space to a real number', "
    "'the Determinant function mapping a square matrix to a real number', etc.\n\n"
    "## Guidelines\n"
    "1. **Conservative Classification**: When in doubt between 'needs_dependencies' and 'impossible', choose 'needs_dependencies'. "
    "Only mark as 'impossible' if the concept fundamentally cannot be expressed in the mathematical framework of the DSL. "
    "When in doubt between 'directly_expressible' and 'needs_dependencies', "
    "choose 'directly_expressible' since the DSL is designed to be expressive enough for these concepts "
    "and you should **TRY YOUR BEST** to find directly expressible formal correspondents for these concepts.\n\n"
    "2. **Direct Correspondents Analysis**: Be precise about what DSL elements (types, relations, functions) can express each concept. "
    "Quote the exact DSL definitions and explain how they relate to the concept.\n\n"
    "3. **Concept Dependencies Analysis**: First of all, **TRY YOUR BEST NOT TO** introduce new concepts unless absolutely necessary!!! "
    "If you must introduce new concepts, note that the list of concepts you are analyzing might have dependencies on each other. "
    "It's great if we can define one concept on top of another, "
    "but be careful about circular dependencies! NO TWO CONCEPTS CAN DEPEND ON EACH OTHER!!!\n\n"
    "4. **Concept Dependencies Criteria**: When adding new mathematical concepts as dependencies, you MUST follow these criteria:\n"
    "   a. **Precision**: When adding new mathematical concepts as dependencies, you MUST be as precise and detailed as possible. "
    "For example 'congruent' is not a precise mathematical relation! "
    "You MUST specify how many arguments and what type of arguments the relation or function takes "
    "like 'two integers being congruent modulo 3', 'two triangles being congruent', 'a list of line segments being congruent to each other', etc.\n"
    "   b. **Well-Definedness**: Please **MAKE SURE** that each mathematical object, relation, and function you add as a dependency is well-defined, "
    "or has a conventionally well-accepted definition. "
    "For example, 'two lines being on oppossing sides of a point' is not well-defined because a point can't partition a plane into sides.\n"
    "   c. **Abstractness**: The definitions, relations and functions you add as a dependency MUST be abstract "
    "i.e. not involving any particular objects, variables, names in the current statements. "
    "For example, 'line AB being parallel to line CD' is not abstract because it involves the names 'AB' and 'CD'.\n\n"
    "4. **Reasoning**: Please carefully examine concept by concept, recall the definition of each concept, "
    "analyze which other concepts are necessary to define the current concept, which of those have direct correspondents in the current DSL, "
    "and provide your detailed step-by-step reasoning **BEFORE** generating the JSON output surrounded by triple angle brackets.\n\n"
    "## Output Format\n"
    "You **MUST** provide your final analysis in JSON format within triple angle brackets. "
    "The JSON should have the following structure:\n\n"
    "```json\n"
    "{{\n"
    '  "concept_name_1": {{\n'
    '    "analysis": "detailed step-by-step reasoning for dependency analysis"\n'
    '    "formal_correspondents": ["list of DSL elements that can express this concept"],\n'
    '    "concept_dependencies": ["list of prerequisite concepts"],\n'
    '    "status": "directly_expressible|needs_dependencies|impossible",\n'
    "  }},\n"
    '  "concept_name_2": {{\n'
    "    ...\n"
    "  }}\n"
    "}}\n"
    "```\n\n"
    "<<< JSON_OUTPUT_HERE >>>\n\n"
    "## Task Context:\n"
    "### **Current DSL Documentation:**\n\n{dsl_doc}\n\n\n\n"
    "### **Previously Analyzed Concepts:**\n\n{previous_analysis}\n\n\n\n"
    "### **Concepts for Analysis:**\n\n{concept_list}\n\n"
)

DSL_EXTENSION_PROMPT = (
    "You are an expert in mathematics, logic, programming languages, and formal verification "
    "with deep knowledge of all fields of mathematics, proof assistants like Lean, and Domain-Specific Language (DSL) design. "
    "You are given a concept dependency graph (CDG) of mathematical concepts, "
    "previous extension file(s) containing the concepts you have already implemented, "
    "and the documentation of a Domain-Specific Language (DSL) for formal mathematics.\n\n"
    "Your task is to extend the current DSL by implementing / formalizing the provided concepts in the CDG based on the current DSL.\n\n"
    "{additional_specs}\n\n"
    "## Guidelines\n"
    "1. **CDG Interpretation**: In the CDG, for each concept, the field 'status' indicates "
    "if we can directly formalize this concept as a relation, function, abbreviation, alias, etc. in the current DSL. "
    "If it is 'directly_expressible', then the field 'formal_correspondents' lists the specific DSL elements that can express this concept. "
    "You **MUST** first try your best to implement the concepts using these 'formal_correspondents'. "
    "However, if they contradicts any specifications given above, "
    "You should carefully use your own knowledge and judgement to determine the most appropriate way to implement "
    "/ formalize each concept based on the current DSL. "
    "If the field 'status' is 'needs_dependencies', then the field 'concept_dependencies' lists the prerequisite concepts "
    "that we need to formalize first before we can formalize this concept. "
    "2. **Faithfulness to Original Concept**: Please try your best to faithfully implement / formalize the original concept, "
    "nothing more and nothing less. For example, if the original concept is a 'a quadrilateral in 2-dimensional Euclidean space', "
    "then you should only invovle the four points and four lines that form the quadrilateral, **no other elements such as the diagonal lines**!!! "
    "Please **PAY EXTRA ATTENTION** to this!!! Such subtlety will result in entirely different formalizations.\n\n"
    "3. **Code Reuse**: Please try your best to reuse the helper functions "
    "or formalized concepts from the previous extension file(s) to implement / formalize the current new concepts. "
    "Please don't reinvent the wheel!!!\n\n"
    "4. **Consistency with Current DSL**: Please ensure your extension matches the current DSL in spirit and style. "
    "For example, naming, API convention, formalization choices, etc.."
    "5. **Documentation**: Please carefully document every "
    "new type, relation, function, axiom, abbrevition, alias, notation, etc. in your implementation. "
    "Please make sure that the style and level of detail are consistent with the current DSL documentation.\n\n"
    "6. **Reasoning**: Please carefully examine concept by concept, analyze the dependency structure of each concept, "
    "determine the best way to implement / formalize each concept based on the current DSL, "
    "and provide your detailed step-by-step reasoning **BEFORE** outputing your final implementation.\n\n"
    "## Output Format\n"
    "You don't need to re-generate the previous extension file(s), **ONLY** output your implementation of the new concepts, "
    "which will be appended to the previous extension file(s). "
    "You **MUST** provide your final implementation within triple angle brackets. "
    "<<< your entire implementation goes here >>>\n\n"
    "## Task Context:\n"
    "### **Current DSL Documentation:**\n\n{dsl_doc}\n\n\n\n"
    "### **Previous Extension File(s):**\n\n{previous_extension_files}\n\n\n\n"
    "### **Concept Dependency Graph (CDG):**\n\n{cdg_list}\n\n"
)

DSL_REFACTORING_PROMPT = (
    "You are an expert in mathematics, logic, programming languages, and formal verification "
    "with deep knowledge of all fields of mathematics, proof assistants like Lean, and Domain-Specific Language (DSL) design. "
    "You are given the documentation of the current Domain-Specific Language (DSL) for formal mathematics "
    "and file(s) containing extensions (new definitions, relations, functions, axioms, theorems, notations, etc.) to this DSL. \n\n"
    "Your task is to refactor the extension file to improve its quality, maintainability, and "
    "consistency with the DSL design principles.\n\n{additional_specs}\n\n"
    "## Guidelines\n"
    "1. **Aggressive Refactoring**: You should be bold in refactoring the extension file:\n"
    "   - **Eliminate Redundancy**: If multiple definitions express the exact same mathematical concept with different levels of generality, "
    "keep only the most general and well-abstracted version.\n"
    "   - **Consolidate Similar Patterns**: When you find multiple similar definitions that can be unified, "
    "remove the individual ones and create a single, parameterized abstraction\n"
    "   - **Quality Over Quantity**: It's better to have fewer, well-designed abstractions than many specific, poorly abstracted ones. "
    "You are not required to preserve every single definition from the original file. "
    "Focus on creating a clean, maintainable, and mathematically sound extension.\n"
    "   - **Pick Best One Only**: If there are many formal relations that are similar to each other, "
    "or can substitute each other, you should either carefully choose one of them, "
    "or merge them into a single, more general and canonical definition. "
    "Multiple similar APIs can be confusing to the user, **BE CONCISE, BE CONCISE, BE CONCISE**!!!\n\n"
    "2. **Preserve The Necessary**: Even though you are required to refactor aggressively, "
    "you should preserve the formal concepts are not truely not in the current DSL. "
    "It's ok if they might be easy to implement using the current DSL primitives, but this "
    "will enhance the readability and further extendability of the DSL.\n\n"
    "3. **Documentation**: Please carefully update the documentation of "
    "every relation, function, axiom, abbrevition, alias, notation, etc. you refactored. "
    "Please make sure that the style and content are consistent with the current DSL documentation, NOT the comments in the extension file(s). "
    "If there are comments in the extension file(s) that are not consistent with the DSL documentation, please refactor them as well.\n\n"
    "4. **Reasoning**: Please carefully analyze the extension file, identify areas for improvement "
    "according to the refactoring criteria, and provide your detailed step-by-step reasoning "
    "**BEFORE** outputting your refactored implementation.\n\n"
    "## Output Format\n"
    "You **MUST** provide your refactored Lean file within triple angle brackets. "
    "The output should be a complete, valid Lean file that can be appended to the DSL. "
    "Do not include any import statements - they will be handled separately.\n\n"
    "<<< your refactored implementation goes here >>>\n\n"
    "## Task Context:\n"
    "### **Current DSL Documentation:**\n\n{dsl_doc}\n\n\n\n"
    "### **Extension File to Refactor:**\n\n{extension_file}\n\n"
)

DSL_DOC_UPDATE_PROMPT = (
    "You are an expert in mathematics, logic, programming languages, and formal verification "
    "with deep knowledge of all fields of mathematics, proof assistants like Lean, and Domain-Specific Language (DSL) design. "
    "You are given the documentation of the current Domain-Specific Language (DSL) for formal mathematics "
    "and extension file(s) containing new definitions, relations, functions, axioms, theorems, notations, etc. "
    "that have been added to this DSL. "
    "Your task is to generate a new DSL documentation to incorporate all the new elements from the extension file(s), "
    "while preserving the previous documentation intact.\n\n{additional_specs}\n\n"
    "## Guidelines\n"
    "1. **Preserve Existing Content**: Keep all existing documentation content unchanged. This is a **MUST**.\n\n"
    "2. **Consistency with Current Doc**: Keep the style and content consistent with the current DSL documentation. "
    "For example, if the current documentation explains the syntax or gives usage examples, then you should do the same.\n\n"
    "3. **Reasoning**: Please carefully analyze the extension file(s), identify all new elements that need to be documented, "
    "determine the best way to integrate them into the existing documentation structure, "
    "and provide your detailed step-by-step reasoning **BEFORE** outputting the new updated DSL documentation.\n\n"
    "## Output Format\n"
    "You **MUST** provide the new DSL documentation within triple angle brackets. "
    "The output should be a complete, new version of the DSL documentation that includes everything: "
    "both elements from the current DSL documentation and new documentation for the extension file(s).\n\n"
    "<<< your entire new DSL documentation goes here >>>\n\n"
    "## Task Context:\n"
    "### **Current DSL Documentation:**\n\n{dsl_doc}\n\n\n\n"
    "### **Extension File(s) to Document:**\n\n{extension_files}\n\n"
)


# ============================================
# STEP 1: Extract and save extracted concepts
# ============================================
def prepare_statement_list(dataset: str) -> list[str]:
    statement_list: list[str] = []

    if dataset == "LeanEuclidPlus":
        # Get the base directory for LeanEuclidPlus dataset
        base_dir = Path(__file__).parent.parent / "LeanEuclidPlus" / "LeanEuclidPlus"

        categories = ["Parallel", "Triangle", "Quadrilateral", "Congruent", "Similarity"]
        for category in categories:
            category_dir = base_dir / category / "clean_texts"

            # Read files 1.txt through 20.txt for each category
            for i in range(1, 21):
                file_path = category_dir / f"{i}.txt"

                if file_path.exists():
                    with open(file_path, "r", encoding="utf-8") as f:
                        statement = f.read().strip()
                        statement_list.append(statement)
                else:
                    print(f"Warning: File not found: {file_path}")

    elif dataset == "ProofNet-Lean4_proof_hard":
        # Get the path to the CSV file
        csv_path = Path(__file__).parent.parent / "data" / "ProofNet-Lean4_proof_hard.csv"

        if not csv_path.exists():
            print(f"Warning: CSV file not found at {csv_path}")
            return statement_list

        # Read the informal statements from the CSV file
        with open(csv_path, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                informal_stmt = row.get("informal_stmt", "").strip()
                if informal_stmt:  # Only add non-empty statements
                    statement_list.append(informal_stmt)

    else:
        raise NotImplementedError(f"Dataset {dataset} not supported yet")

    print(f"Loaded {len(statement_list)} statements from {dataset}")

    return statement_list


def extract_concept_single_batch(
    dataset: str,
    statement_list: list[str],
    previous_concepts: list[str],
    llm: UnifiedModel,
    num_attempts: int = 5,
) -> tuple[str, list[str], list[str]]:
    # Add additional specs for the dataset
    if dataset == "LeanEuclidPlus":
        additional_specs = (
            "The statements are in the context of 2-Dimensional Euclidean Geometry. "
            "All points and lines mentioned in the statements are distinct, "
            "unless otherwise implied by some premises."
        )
    elif dataset == "ProofNet-Lean4_proof_hard":
        additional_specs = (
            "The statements are in the context of standard undergraduate mathematics, "
            "including Real Analysis, Complex Analysis, Linear Algebra, "
            "Abstract Algebra, Topology, Number Theory, etc."
        )
    else:
        raise NotImplementedError(f"Dataset {dataset} not supported yet")

    # Format the previous concept list as pretty JSON for the LLM
    previous_concepts_pretty = json.dumps(previous_concepts, indent=4, ensure_ascii=False)
    # Concatenate statements in the list into a single string
    english_statements = "\n\n\n".join(statement_list)
    # Construct the prompt for concept extraction
    prompt = CONCEPT_EXTRACTION_PROMPT.format(
        previous_concepts=previous_concepts_pretty,
        english_statements=english_statements,
        additional_specs=additional_specs,
    )

    # Prepare messages for LLM
    messages: Messages = [{"role": "user", "content": [{"type": "input_text", "text": prompt}]}]

    for i in range(num_attempts):
        print(f"Attempting concept extraction (attempt {i+1}/{num_attempts})...")

        # Get response from model
        response_text, _, reasoning_summary_list, _ = llm.get_response(None, messages)

        # Add the assistant response to the context
        messages.append({"role": "assistant", "content": [{"type": "output_text", "text": response_text}]})

        # CHECK 1: The response must be surrounded by triple angle brackets
        pattern = r"<<<(.*?)>>>"
        matches = re.findall(pattern, response_text, re.DOTALL)
        if not matches:
            feedback = (
                "I couldn't find your extracted concepts in the expected format. "
                "Please make sure to provide your final extraction answer within **triple angle brackets** "
                "and separated by semi-colons: <<< concept1; concept2; ... >>>"
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            print(f"⚠️  Warning: can't find triple angle brackets in {response_text}, making attempt number {i+1} ...")
            continue

        # CHECK 2: The response must be either a single concept or semicolon-separated list of concepts
        model_prediction = matches[-1].strip()
        # Allow either single concept or semicolon-separated list: "concept1" or "concept1; concept2; ..."
        pattern = r"^[^;]+(?:;\s*[^;]+)*$"
        if not re.match(pattern, model_prediction):
            feedback = (
                f"Invalid concept format '{model_prediction}'. "
                "Each concept should be in format 'concept1' or 'concept1; concept2; ...'. Please provide your selection again."
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            print(f"⚠️  Warning: invalid concept format '{model_prediction}', making attempt number {i+1} ...")
            continue

        # Save the concepts into a list
        extracted_concepts = model_prediction.split(";")
        extracted_concepts = [concept.strip() for concept in extracted_concepts]

        return response_text, reasoning_summary_list, extracted_concepts

    # If all attempts failed, return empty results
    print("⚠️  Warning: All concept extraction attempts failed, returning empty concepts")
    return "", [], []


def extract_concept_all_sequential(
    dataset: str,
    statement_list: list[str],
    batch_size: int,
    llm: UnifiedModel,
    num_attempts: int = 5,
    save_log: bool = True,
) -> dict[str, int]:
    # Initailize the concept dictionary and log list if needed
    concept_dict: dict[str, int] = {}
    if save_log:
        log_list: list[dict[str, Any]] = []

    # Batch the statements list into a list of batches
    statement_batch_list: list[list[str]] = []
    for i in range(0, len(statement_list), batch_size):
        statement_batch_list.append(statement_list[i : i + batch_size])

    # Initialize progress bar for concept extraction
    extraction_pbar = tqdm(total=len(statement_batch_list), desc="Extracting concepts", unit="batch", position=0, leave=True)

    for index, statement_batch in enumerate(statement_batch_list):
        # Get current list of concepts (keys from dict)
        current_concepts = list(concept_dict.keys())

        # Extract concepts from current statement
        response_text, reasoning_summary_list, extracted_concepts = extract_concept_single_batch(
            dataset, statement_batch, current_concepts, llm, num_attempts=num_attempts
        )

        # Update the shared concept dictionary
        for concept in extracted_concepts:
            if concept in concept_dict:
                concept_dict[concept] += 1
            else:
                concept_dict[concept] = 1

        print(f"Extracted concepts: {extracted_concepts}")
        print(f"Current concept count: {len(concept_dict)}")

        # Update progress bar after batch completion
        print()  # Add blank line before progress bar update
        extraction_pbar.update(1)
        extraction_pbar.set_description(f"Batch {index + 1}/{len(statement_batch_list)} - Concepts: {len(concept_dict)}")
        print()  # Add blank line after progress bar update

        # Log the state of the extraction
        if save_log:
            log_list.append(
                {
                    "batch_index": index + 1,
                    "statement_batch": statement_batch,
                    "llm_reasoning": reasoning_summary_list,
                    "llm_response": response_text,
                    "extracted_concepts": extracted_concepts,
                    "concepts_dict": concept_dict,
                }
            )

    # Close extraction progress bar
    print()  # Add blank line before final progress bar update
    extraction_pbar.set_description(f"Extraction Complete - {len(statement_batch_list)} batches, {len(concept_dict)} concepts")
    extraction_pbar.close()
    print()  # Add blank line after progress bar closes

    # Sort the concept dictionary by frequency in descending order
    sorted_concept_dict = dict(sorted(concept_dict.items(), key=lambda x: x[1], reverse=True))

    # If save_log is True, save the log list to a json file
    if save_log:
        with open(f"concept_extraction_log_{dataset}.json", "w", encoding="utf-8") as f:
            json.dump(log_list, f, ensure_ascii=False, indent=2)

    return sorted_concept_dict


# ============================================
# STEP 2: Filter Extracted Concepts
# ============================================
def filter_extracted_concepts(
    dataset: str,
    concept_dict: dict[str, int],
    llm: UnifiedModel,
    threshold: int = 0,
    num_iterations: int = 1,
    num_attempts: int = 5,
    save_log: bool = True,
) -> dict[str, int]:
    # Step 1: Filter by threshold
    print(f"Applying threshold filtering with count threshold {threshold} ...")
    concept_dict_threshold = {concept: count for concept, count in concept_dict.items() if count >= threshold}

    print("=" * 60)
    print(f"Original Concept Count: {len(concept_dict)}")
    print(f"Threshold Filtered Out Count: {len(concept_dict) - len(concept_dict_threshold)}")
    print(f"After Threshold Filtering Count: {len(concept_dict_threshold)}")
    print("=" * 60)

    if not concept_dict_threshold:
        print("No concepts remaining after threshold filtering")
        return {}

    # Step 2: LLM-based quality and redundancy filtering
    concept_list = list(concept_dict_threshold.keys())

    # Load the DSL documentation
    if dataset == "LeanEuclidPlus":
        dsl_doc_path = (
            Path(__file__).parent.parent / "LeanEuclidPlus" / "AutoFormalization" / "statement" / "instructions" / "doc_barebone.txt"
        )
    elif dataset == "ProofNet-Lean4_proof_hard":
        dsl_doc_path = Path(__file__).parent / "ProofNetHard" / "doc_barebone.txt"
    else:
        raise NotImplementedError(f"Dataset {dataset} not supported yet")

    try:
        with open(dsl_doc_path, "r", encoding="utf-8") as f:
            dsl_doc = f.read().strip()
    except FileNotFoundError:
        print(f"Warning: DSL doc not found at {dsl_doc_path}, using empty DSL doc")
        dsl_doc = ""

    # Add additional specs for the dataset
    additional_specs = ""
    if dataset == "LeanEuclidPlus":
        additional_specs = (
            "The concepts are in the context of 2-Dimensional Euclidean Geometry. "
            "The current DSL implements a formal system of 2-Dimensional Euclidean Geometry in Lean 4."
        )
    elif dataset == "ProofNet-Lean4_proof_hard":
        additional_specs = (
            "## Background\n"
            "The statements are in the context of standard undergraduate mathematics, "
            "including Real Analysis, Complex Analysis, Linear Algebra, "
            "Abstract Algebra, Topology, Number Theory, etc. "
            "## Mathematical Concepts\n"
            "There are 3 types of mathematical concepts to keep:\n"
            "1. **Definitions of Mathematical Objects**: Point, Line, Integer, Real Number, Series, Group, Ring, etc.\n"
            "2. **Relations between Mathematical Objects**: 'a point being on a line', "
            "'an integer being even', 'a group being a subgroup of another group', etc.\n"
            "3. **Functions mapping Mathematical Objects to Mathematical Objects**: "
            "'the Euclidean distance function mapping two points in Euclidean space to a real number', "
            "'the Determinant function mapping a square matrix to a real number', etc.\n\n"
            "4. **No Theorem, Lemma, Corollary, etc.**: Please only keep definitions, relations and functions, "
            "and avoid theorem, lemma, corollary, proposition, property, and specific problems etc.\n\n"
            "## Principles\n"
            "Most of the concepts should have direct formal correspondents in Mathlib, "
            "so please recall your knowledge of Mathlib and Lean 4 (version specified below) "
            "to filter out concepts **AS MANY AS POSSIBLE** following the guidelines."
        )

    # Initialize logging if requested
    log_list: list[dict[str, Any]] = [] if save_log else []
    current_concept_dict = concept_dict_threshold.copy()

    # Iteratively filter for `num_iterations` times
    for i in range(num_iterations):
        print("=" * 80)
        print(f"Concept Filtering Iteration {i+1}/{num_iterations}...")
        print("=" * 80)

        # Format the previous concept list as pretty JSON for the LLM
        concept_list_current_pretty = json.dumps(current_concept_dict, indent=4, ensure_ascii=False)
        # Construct the prompt for concept filtering
        prompt = CONCEPT_FILTERING_PROMPT.format(
            additional_specs=additional_specs,
            dsl_doc=dsl_doc,
            concept_list=concept_list_current_pretty,
        )

        # Prepare messages for LLM
        messages: Messages = [{"role": "user", "content": [{"type": "input_text", "text": prompt}]}]

        # Try LLM filtering with retries
        iteration_success = False
        for j in range(num_attempts):
            print(f"Attempting filtering (attempt {j+1}/{num_attempts})...")

            # Get response from model
            response_text, _, reasoning_summary_list, _ = llm.get_response(None, messages)

            # Add the assistant response to the context
            messages.append({"role": "assistant", "content": [{"type": "output_text", "text": response_text}]})

            # CHECK 1: The response must be surrounded by triple angle brackets
            pattern = r"<<<(.*?)>>>"
            matches = re.findall(pattern, response_text, re.DOTALL)
            if not matches:
                feedback = (
                    "I couldn't find your filtered concepts in the expected format. "
                    "Please make sure to provide your final filtering decision within **triple angle brackets** "
                    "and separated by semi-colons: <<< concept1; concept2; ... >>>"
                )
                messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
                print(f"⚠️  Warning: can't find triple angle brackets in response, making attempt number {j+1} ...")
                continue

            # CHECK 2: Parse the filtered concepts
            model_prediction = matches[-1].strip()
            # Handle empty filtering result (no concepts to filter out)
            if not model_prediction:
                print("No concepts to filter out")
                concepts_to_filter_out = []
            else:
                # Allow either single concept or semicolon-separated list
                pattern = r"^[^;]+(?:;\s*[^;]+)*$"
                if not re.match(pattern, model_prediction):
                    feedback = (
                        f"Invalid concept format '{model_prediction}'. "
                        "Each concept should be in format 'concept1' or 'concept1; concept2; ...'. Please provide your selection again."
                    )
                    messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
                    print(f"⚠️  Warning: invalid concept format '{model_prediction}', making attempt number {j+1} ...")
                    continue
                # Parse the filtered concepts
                concepts_to_filter_out = model_prediction.split(";")
                concepts_to_filter_out = [concept.strip() for concept in concepts_to_filter_out if concept.strip()]

            # CHECK 3: Verify that all filtered concepts were in the original concept list
            invalid_concepts = [concept for concept in concepts_to_filter_out if concept not in concept_list]
            if invalid_concepts:
                feedback = (
                    f"The following concepts in your response were not in the original list: {invalid_concepts}. "
                    "Please only include concepts from the provided list."
                )
                messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
                print(f"⚠️  Warning: invalid concepts in response: {invalid_concepts}, making attempt number {j+1} ...")
                continue

            # Create the final filtered concept dictionary by removing concepts to filter out
            concept_dict_filtered = {concept: count for concept, count in current_concept_dict.items() if concept not in concepts_to_filter_out}

            print("=" * 60)
            print(f"After Previous Filtering Count: {len(current_concept_dict)}")
            print(f"LLM Filtered Out Count: {len(concepts_to_filter_out)}")
            print(f"Final Concept Count: {len(concept_dict_filtered)}")
            print("=" * 60)

            # Save the log and break the loop
            if save_log:
                log_data = {
                    "iteration_number": i + 1,
                    "concepts_dict_original": concept_dict_threshold,
                    "llm_reasoning": reasoning_summary_list,
                    "llm_response": response_text,
                    "llm_filtered_out": concepts_to_filter_out,
                    "concepts_dict_filtered": concept_dict_filtered,
                    "attempts_used": j + 1,
                    "success": True,
                }
                log_list.append(log_data)

            # Update the current concept dictionary
            current_concept_dict = concept_dict_filtered.copy()
            iteration_success = True
            break

        # If all attempts failed for this iteration, log the failure
        if not iteration_success:
            print("⚠️  Warning: LLM filtering failed after 3 attempts, falling back to threshold filtering only")

            if save_log:
                log_data = {
                    "iteration_number": i + 1,
                    "concepts_dict_original": concept_dict,
                    "threshold": threshold,
                    "concepts_dict_threshold": concept_dict_threshold,
                    "llm_reasoning": reasoning_summary_list,
                    "llm_response": response_text,
                    "llm_filtered_out": concepts_to_filter_out,
                    "total_attempts": num_attempts,
                    "success": False,
                    "final_error": "All attempts failed for this iteration",
                }
                log_list.append(log_data)

            # Update the current concept dictionary and exit the outer loop
            current_concept_dict = concept_dict_threshold.copy()
            break

    # Save the log
    with open(f"concept_filtering_log_{dataset}.json", "w", encoding="utf-8") as f:
        json.dump(log_data, f, ensure_ascii=False, indent=2)
    print(f"Filtering log saved to concept_filtering_log_{dataset}.json")

    return current_concept_dict


# ============================================
# STEP 3: Construct Concept Dependency Graph (CDG)
# ============================================
def construct_cdg_single_batch(
    dataset: str,
    concept_list: list[str],
    previous_analysis: dict[str, dict[str, Any]],
    llm: UnifiedModel,
    num_attempts: int = 5,
) -> tuple[str, list[str], dict[str, dict[str, Any]]]:
    print("Constructing concept dependency graph...")
    print(f"Analyzing {len(concept_list)} concepts...")

    # Load the DSL documentation
    if dataset == "LeanEuclidPlus":
        dsl_doc_path = (
            Path(__file__).parent.parent / "LeanEuclidPlus" / "AutoFormalization" / "statement" / "instructions" / "doc_barebone.txt"
        )
    elif dataset == "ProofNet-Lean4_proof_hard":
        dsl_doc_path = Path(__file__).parent / "ProofNetHard" / "doc_barebone.txt"
    else:
        raise NotImplementedError(f"Dataset {dataset} not supported yet")

    try:
        with open(dsl_doc_path, "r", encoding="utf-8") as f:
            dsl_doc = f.read().strip()
    except FileNotFoundError:
        print(f"Warning: DSL doc not found at {dsl_doc_path}, using empty DSL doc")
        dsl_doc = ""

    # Construct the prompt for concept dependency analysis
    additional_specs = ""
    if dataset == "LeanEuclidPlus":
        additional_specs = (
            "The concepts are in the context of 2-Dimensional Euclidean Geometry. "
            "The current DSL implements a formal system of 2-Dimensional Euclidean Geometry in Lean 4. "
            "You should **KEEP IN MIND** that when trying to find directly formal correspondents "
            "for a concept, you can leverage both the DSL and primitives in Lean 4, but **NOT** any other libraries!!!"
        )
    elif dataset == "ProofNet-Lean4_proof_hard":
        additional_specs = (
            "The concepts are in the context of standard undergraduate mathematics, "
            "including Real Analysis, Complex Analysis, Linear Algebra, "
            "Abstract Algebra, Topology, Number Theory, etc. "
            "Most of the concepts should be able to be directly formalized using exisiting formal correspondents in Mathlib, "
            "so please recall your knowledge of Mathlib and Lean 4 (version specified below). "
            "You should **KEEP IN MIND** that when trying to find directly formal correspondents "
            "for a concept, you can leverage both Mathlib and primitives in Lean 4, but **NOT** any other libraries!!!"
        )

    # Format the concept list as pretty JSON for the LLM
    concept_list_pretty = json.dumps(concept_list, indent=4, ensure_ascii=False)

    # Format previously analyzed concepts (without analysis field for brevity)
    previous_analysis_summary = {}
    for concept_name, concept_data in previous_analysis.items():
        previous_analysis_summary[concept_name] = {
            "status": concept_data.get("status", ""),
            "formal_correspondents": concept_data.get("formal_correspondents", []),
            "concept_dependencies": concept_data.get("concept_dependencies", []),
        }
    previous_analysis_pretty = json.dumps(previous_analysis_summary, indent=4, ensure_ascii=False)

    # Construct the prompt for CDG construction
    prompt = CDG_CONSTRUCTION_PROMPT.format(
        additional_specs=additional_specs,
        dsl_doc=dsl_doc,
        previous_analysis=previous_analysis_pretty,
        concept_list=concept_list_pretty,
    )

    # Prepare messages for LLM
    messages: Messages = [{"role": "user", "content": [{"type": "input_text", "text": prompt}]}]

    # Try dependency analysis with retries
    for i in range(num_attempts):
        print(f"Attempting CDG construction (attempt {i+1}/{num_attempts})...")

        # Get response from model
        response_text, _, reasoning_summary_list, _ = llm.get_response(None, messages)

        # Add the assistant response to the context
        messages.append({"role": "assistant", "content": [{"type": "output_text", "text": response_text}]})

        # CHECK 1: The response must be surrounded by triple angle brackets
        pattern = r"<<<(.*?)>>>"
        matches = re.findall(pattern, response_text, re.DOTALL)
        if not matches:
            feedback = (
                "I couldn't find your dependency analysis in the expected format. "
                "Please make sure to provide your analysis in JSON format within **triple angle brackets**: "
                '<<< {"concept1": {...}, "concept2": {...}} >>>'
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            print(f"⚠️  Warning: can't find triple angle brackets in response, making attempt number {i+1} ...")
            continue

        # CHECK 2: Parse the JSON response
        model_prediction = matches[-1].strip()
        try:
            dependency_graph = cast(dict[str, dict[str, Any]], json.loads(model_prediction))
        except json.JSONDecodeError as e:
            feedback = f"Invalid JSON format in your response: {e}. " "Please provide a valid JSON object with the specified structure."
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            print(f"⚠️  Warning: invalid JSON format, making attempt number {i+1} ...")
            continue

        # CHECK 3: Validate the structure of the dependency graph
        validation_errors = []
        required_fields = ["status", "formal_correspondents", "concept_dependencies", "analysis"]
        valid_statuses = ["directly_expressible", "needs_dependencies", "impossible"]

        for concept_name, concept_data in dependency_graph.items():
            # Check required fields
            for field in required_fields:
                if field not in concept_data:
                    validation_errors.append(f"Concept '{concept_name}' missing required field '{field}'")

            # Check status field
            if "status" in concept_data and concept_data["status"] not in valid_statuses:
                validation_errors.append(f"Concept '{concept_name}' has invalid status '{concept_data['status']}'")

            # Check that formal_correspondents and concept_dependencies are lists
            if "formal_correspondents" in concept_data and not isinstance(concept_data["formal_correspondents"], list):
                validation_errors.append(f"Concept '{concept_name}' formal_correspondents should be a list")

            if "concept_dependencies" in concept_data and not isinstance(concept_data["concept_dependencies"], list):
                validation_errors.append(f"Concept '{concept_name}' concept_dependencies should be a list")

        # CHECK 4: Ensure all input concepts are analyzed
        missing_concepts = set(concept_list) - set(dependency_graph.keys())
        if missing_concepts:
            validation_errors.append(f"Missing analysis for concepts: {list(missing_concepts)}")

        if validation_errors:
            feedback = (
                "Validation errors in your response:\n"
                + "\n".join(f"- {error}" for error in validation_errors)
                + "\n\nPlease fix these issues and provide the analysis again."
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            print(f"⚠️  Warning: validation errors, making attempt number {i+1} ...")
            continue

        # Success! Return results
        print(f"✅ Batch analysis completed! Analyzed {len(dependency_graph)} concepts")
        return response_text, reasoning_summary_list, dependency_graph

    # If all attempts failed, return empty results
    print("⚠️  Warning: All dependency analysis attempts failed, returning empty results")
    return "", [], {}


def construct_cdg_all_sequential(
    dataset: str,
    concept_list: list[str],
    batch_size: int,
    llm: UnifiedModel,
    num_attempts: int = 5,
    save_log: bool = True,
) -> dict[str, dict[str, Any]]:
    # Initialize tracking variables
    all_analysis: dict[str, dict[str, Any]] = {}
    concept_queue = concept_list.copy()  # Concepts waiting to be analyzed
    analyzed_concepts: set[str] = set()  # Concepts that have been analyzed
    batch_count = 0

    # Initialize logging if requested
    if save_log:
        log_list: list[dict[str, Any]] = []

    # Initialize progress bar for batch processing
    pbar = tqdm(desc="CDG Batches", unit="batch", dynamic_ncols=True, position=0, leave=True)

    # Process concepts until termination condition is met
    while concept_queue:
        batch_count += 1

        print(f"\n================== BATCH {batch_count} ==================")
        print(f"Concepts in queue: {len(concept_queue)}")
        print(f"Previously analyzed: {len(analyzed_concepts)}")
        print("==========================================================")

        # Get current batch (remove duplicates and already analyzed concepts)
        current_batch: list[str] = []
        remaining_queue: list[str] = []

        for concept in concept_queue:
            if concept not in analyzed_concepts and concept not in current_batch:
                if len(current_batch) < batch_size:
                    current_batch.append(concept)
                else:
                    remaining_queue.append(concept)
            elif concept not in analyzed_concepts:
                remaining_queue.append(concept)

        concept_queue = remaining_queue

        if not current_batch:
            print("No new concepts to analyze in this batch.")
            break

        print(f"Analyzing batch: {current_batch}")

        # Analyze current batch
        batch_response_text, batch_reasoning_summary, batch_analysis = construct_cdg_single_batch(
            dataset=dataset, concept_list=current_batch, previous_analysis=all_analysis, llm=llm, num_attempts=num_attempts
        )

        # Update global analysis and tracking
        all_analysis.update(batch_analysis)
        analyzed_concepts.update(current_batch)

        # Find concepts that need dependencies and extract new concepts
        new_dependencies = set()
        needs_deps_concepts = []

        for concept_name, concept_data in batch_analysis.items():
            if concept_data.get("status") == "needs_dependencies":
                needs_deps_concepts.append(concept_name)
                deps = concept_data.get("concept_dependencies", [])
                for dep in deps:
                    # Only add new dependencies to the queue if they are not already analyzed or in the queue
                    if dep not in analyzed_concepts and dep not in concept_queue:
                        new_dependencies.add(dep)

        # Add new dependencies to queue
        if new_dependencies:
            print(f"Found {len(new_dependencies)} new dependencies: {list(new_dependencies)}")
            concept_queue.extend(list(new_dependencies))

        # Print batch summary
        batch_status_counts = {"directly_expressible": 0, "needs_dependencies": 0, "impossible": 0}
        for concept_data in batch_analysis.values():
            status = concept_data.get("status", "unknown")
            if status in batch_status_counts:
                batch_status_counts[status] += 1

        print(f"Batch results: {batch_status_counts}")

        # Update progress bar after batch completion
        print()  # Add blank line before progress bar
        pbar.update(1)
        if new_dependencies:
            pbar.set_description(
                f"Batch {batch_count} - Queue: {len(concept_queue)}, Analyzed: {len(analyzed_concepts)} (+{len(new_dependencies)} deps)"
            )
        else:
            pbar.set_description(f"Batch {batch_count} - Queue: {len(concept_queue)}, Analyzed: {len(analyzed_concepts)}")
        print()  # Add blank line after progress bar

        # Log batch information
        if save_log:
            log_list.append(
                {
                    "batch_index": batch_count,
                    "concepts_analyzed": current_batch,
                    "llm_reasoning": batch_reasoning_summary,
                    "llm_response": batch_response_text,
                    "batch_analysis": batch_analysis,
                    "new_dependencies_found": list(new_dependencies),
                    "queue_after_batch": concept_queue.copy(),
                    "batch_status_summary": batch_status_counts,
                }
            )

        # Check termination condition: queue is empty (all concepts analyzed)
        if not concept_queue:
            print("✅ All concepts have been analyzed!")
            break

        # Additional check: if no new dependencies were found and no concepts need dependencies,
        # we might have reached a stable state
        if not new_dependencies and not needs_deps_concepts:
            # Check if all remaining concepts in queue are duplicates or already analyzed
            remaining_new_concepts = [c for c in concept_queue if c not in analyzed_concepts]
            if not remaining_new_concepts:
                print("✅ All concepts resolved - no new concepts to analyze!")
                break

        # Safety check to prevent infinite loops
        if batch_count > 50:  # Reasonable upper limit
            print("⚠️  Warning: Reached maximum batch limit (50), stopping to prevent infinite loop")
            break

    # Final progress bar update and close
    print()  # Add blank line before final progress bar update
    pbar.set_description(f"CDG Complete - {batch_count} batches, {len(analyzed_concepts)} concepts analyzed")
    pbar.close()
    print()  # Add blank line after progress bar closes

    # Final summary
    final_status_counts = {"directly_expressible": 0, "needs_dependencies": 0, "impossible": 0}
    for concept_data in all_analysis.values():
        status = concept_data.get("status", "unknown")
        if status in final_status_counts:
            final_status_counts[status] += 1

    print("\n" + "=" * 80)
    print("FINAL CDG CONSTRUCTION SUMMARY")
    print("=" * 80)
    print(f"Total batches processed: {batch_count}")
    print(f"Total concepts analyzed: {len(all_analysis)}")
    print(f"Final status distribution: {final_status_counts}")
    print("=" * 80)

    # If save_log is True, save the log list to a json file
    if save_log:
        with open(f"cdg_construction_log_{dataset}.json", "w", encoding="utf-8") as f:
            json.dump(log_list, f, ensure_ascii=False, indent=2)

    return all_analysis


# ============================================
# STEP 4: Extend The DSL
# ============================================
def extend_dsl_single_batch(
    dataset: str,
    cdg_list: list[dict[str, Any]],
    previous_extension_files: str,
    llm: UnifiedModel,
    num_attempts: int = 5,
) -> tuple[str, list[str], str]:
    # Set the Lean project root directory, and
    # load the DSL documentation that the model should extend
    if dataset == "LeanEuclidPlus":
        root_dir = ROOT_DIR_LeanEuclidPlus
        dsl_doc_path = (
            Path(__file__).parent.parent / "LeanEuclidPlus" / "AutoFormalization" / "statement" / "instructions" / "doc_barebone.txt"
        )
        header = "import SystemE.Theory.Relations"
    elif dataset == "ProofNet-Lean4_proof_hard":
        root_dir = ROOT_DIR_PROOFNET
        dsl_doc_path = Path(__file__).parent / "ProofNetHard" / "doc_barebone.txt"
        header = "import Mathlib"
    else:
        raise NotImplementedError(f"Dataset {dataset} not supported yet")

    try:
        with open(dsl_doc_path, "r", encoding="utf-8") as f:
            dsl_doc = f.read().strip()
    except FileNotFoundError:
        dsl_doc = ""

    # Add additional specs for the dataset
    additional_specs = ""
    if dataset == "LeanEuclidPlus":
        additional_specs = (
            "## DSL Extension\n"
            "1. **Background**: All concepts are in the context of 2-Dimensional Euclidean Geometry. "
            "The current DSL implements a formal system of 2-Dimensional Euclidean Geometry in Lean 4. "
            "To implement a concept, you can leverage both the DSL and primitives in Lean 4 (NOT other libraries).\n\n"
            "2. **No External Imports**: Please do not add any external imports, you are **ONLY** allowed to use what is provided in the "
            "current DSL and some primitives in Lean 4 (there are restrictions on what you can use). "
            "The import header for the current DSL will have handled later, so you should not include **ANY** import statements in your output!!!\n\n"
            "3. **Proper Namespace**: Please choose the proper namespace of to implement the geometric concept. "
            "If the concept is about the relation between one main-focus object and other objects, "
            "for example, 'a point being on a line', 'a point being on a circle', then you should choose the namespace 'Point'. "
            "Your user will use the syntax `a.onLine L`, `a.onCircle C`, etc. to invoke these relations.\n\n"
            "If the concepts is about the relation between multiple objects with no obvious main focus, "
            "for example, 'three points and three lines forming a proper triangle', "
            "then you should make it a general relation in no specific namespaces. "
            "You user will use the syntax `formTriangle a b c A B C` to invoke this relation. "
            "For complex relation, you should prioritize no namespaces. \n\n"
            "4. **No New Types**: The refactored file should not introduce any new types. "
            "You **MUST** only use the types provided in the current DSL and Lean 4 primitives.\n\n"
            "5. **No Quantifiers**: To implement a concept, you can't use any quantifiers i.e. "
            "the exsistential quantifier '∃' or the universal quantifier '∀'. "
            "For example, when formalizing the concept 'inverse of a function', you shouldn't use existential quantifier in your implementation. "
            "Instead, you should let the user explicitly give the inverse function as a parameter like "
            "`inverseOfEachOther (f : A → B) (g : B → A) : Prop`. "
            "For another example, when formalizing the concept 'two lines intersecting at a point', "
            "you shouldn't use existential quantifier in your implementation. "
            "Instead, you should let the user explicitly give the intersection point as a parameter like "
            "`twoLinesIntersectAtPoint (L1 L2 : Line) (i: Point) : Prop`. "
            "This is **EXTREMELY CRITICAL**, please double check and pay extra attention to the example!!!\n\n"
            "6. **No Disjunction**: To implement a concept, you can't use any disjunction i.e. '∨'. "
            "in your formula. You **MUST** let the user explicitly specify which Point, Line, or Circle makes this relation hold. "
            "For example, when formalizing the concept 'a line segment bisecting an angle at its vertex', "
            "you should let the user explicitly specify a point on the line segement other than the vertex as a parameter. "
            "This is **EXTREMELY CRITICAL**, please double check and pay extra attention to the example!!!\n\n"
            "7. **Proper Implementation**: A concept can be implemented as simple as an alias of "
            "some existing formal relation or function in the current DSL, "
            "or an abbreviation of a quantifier-free formulas in the current DSL, "
            "or a recursive function based on itself and some existing formal relations or functions in the current DSL, etc. "
            "Please pick the simplest andmost appropriate way to implement each concept based on the current DSL. "
            "For example, when formalizing a concept involving 'two or more', 'three or more', 'a set of', 'a list of', etc., "
            "you can consider using a recursive function to capture the idefinite number of elements or objects. "
            "Please free to define any helper functions or relations as needed. "
            "Remember, **NO QUANTIFIERS**!!!\n\n"
            "8. **Angle Measures**: In our DSL, the right angle denoted by '∟' "
            "is defined as an opaque constant with no explicit value. "
            "You **MUST** use this opaque constant rather than using any explicit values. "
            "For example, the measure of 180 degrees is represented by '∟ + ∟' rather than '180'. "
            "This is **EXTREMELY CRITICAL**, please double check and pay extra attention to the example!!!\n\n"
            "9. **Use Canonical Definition**: Please always use the most conventional and canonical definition of the mathematical concept. "
            "For example, there are many criteria for triangle similarity like AAA or SAS,"
            "but you should merge them into the canonical definition that states that **all corresponding angles of T1 and T2 are equal, "
            "and all corresponding sides of T1 and T2 are equally proportional.** "
            "You should implemnent the merged defintion in the simplest way possible: for triangle abc and def, "
            "ab / de = bc / ef = ca / fd , etc. "
            "Same as triangle congruence, you shouldn't pick any arbitrary criterion alone as the definition. "
            "Instead, you should merge them into the canonical definition that states that **all corresponding angles of T1 and T2 are equal, "
            "and all corresponding sides of T1 and T2 are equal.** "
            "Please **PAY EXTRA ATTENTION** to the examples!!!\n\n"
            "10. **Tactic Registration**: Please register the new relations, function, abbrevitions, aliases, etc. under the `simp` tactic. "
            "For example, ```@[simp]\ndef my_relation (a b c : Point) : Prop ...\n```\n\n"
        )
    elif dataset == "ProofNet-Lean4_proof_hard":
        additional_specs = (
            "## DSL Extension\n"
            "1. **Background**: All concepts are in the context of standard undergraduate mathematics, "
            "including Real Analysis, Complex Analysis, Linear Algebra, "
            "Abstract Algebra, Topology, Number Theory, etc. "
            "You should **KEEP IN MIND** that when trying to find directly formal correspondents "
            "you can leverage **EVERYTHING** in Mathlib and primitives in Lean 4 (NOT other libraries).\n\n"
            "2. **No External Imports**: Please do not add any external imports, you are **ONLY** allowed to use what is provided in Mathlib.\n\n"
            "3. **Proper Scope & Section**: Please open the proper scope for each section, "
            "so that it's easier to use primitives in certain Mathlib modules\n"
            "Example 1: `open Real Complex Filter Set TopologicalSpace ...` to bring constants and definitions "
            "from like Real.sqrt into the current scope, so you can just use sqrt directly instead of Real.sqrt.\n"
            "Example 2: `open scoped NNReal` if you want to use ℝ≥0. `open scoped` turns on localized notation/instances "
            "that were declared for the notation scope.\n"
            "Example 3: Use the `noncomputable` keyword properly for sections containing noncomputable definitions.\n"
            "Please **PAY EXTRA ATTENTION** to the examples below!!! You **MUST** open the proper scope for each section!!! "
            "Last but not the least, you don't need to write `import Mathlib` in the beginning of the file, "
            "this will be added later.\n\n"
            "4. **Proper Formalization**: \n"
            "   a. Please pick the simplest andmost appropriate way to implement each concept based on the current DSL. "
            "For example, when formalizing a concept involving 'two or more', 'three or more', 'a set of', 'a list of', etc., "
            "you can consider using a recursive function to capture the idefinite number of elements or objects.\n"
            "   b. Please free to define any helper functions or relations as needed.\n"
            "   c. However, you should **NOT** formalize any concept as axioms, theorems, lemmas, examples, etc.\n"
            "   d. For some concepts, the formal correspondents might not be available in the specific version of Mathlib and Lean "
            "that we are using. Please **SEEK ALTERNATIVES** if you see related error messages or get stuck.\n"
            "Please **PAY EXTRA ATTENTION** to this **Proper Formalization** specification in particular!!!\n\n"
            "5. **Tactic Registration**: Please register the new relations, function, abbrevitions, aliases, etc. under the `simp` tactic. "
            "For example, ```@[simp]\ndef my_relation (a b c : Point) : Prop ...\n```\n\n"
        )

    # Remove the concetps with status "impossible" from the CDG
    cdg_list = [cdg for cdg in cdg_list if cdg["status"] != "impossible"]
    # Remove the "analysis" field from the CDG
    for cdg in cdg_list:
        cdg.pop("analysis", None)
    # Format the CDG as pretty JSON for the LLM
    cdg_list_pretty = json.dumps(cdg_list, indent=4, ensure_ascii=False)
    print(cdg_list_pretty)
    # Construct the prompt for DSL extension
    prompt = DSL_EXTENSION_PROMPT.format(
        additional_specs=additional_specs,
        dsl_doc=dsl_doc,
        previous_extension_files=previous_extension_files,
        cdg_list=cdg_list_pretty,
    )

    # Prepare messages for LLM
    messages: Messages = [{"role": "user", "content": [{"type": "input_text", "text": prompt}]}]

    # Prepare validator directories
    tmp_dir = os.path.join(root_dir, "tmp", "dsl_extension")
    os.makedirs(tmp_dir, exist_ok=True)
    validator = Validator(
        root_dir=root_dir,
        tmp_dir=tmp_dir,
        relations_file="",  # no need, since we only need the method `validate_lean_file`
    )

    # Try DSL extension with validation feedback loop
    for i in range(num_attempts):
        print(f"Attempting DSL extension (attempt {i+1}/{num_attempts})...")

        # Get response from model
        response_text, _, reasoning_summary_list, _ = llm.get_response(None, messages)

        # Add the assistant response to the context
        messages.append({"role": "assistant", "content": [{"type": "output_text", "text": response_text}]})

        # CHECK 1: The response must be surrounded by triple angle brackets
        pattern = r"<<<(.*?)>>>"
        matches = re.findall(pattern, response_text, re.DOTALL)
        if not matches:
            feedback = (
                "I couldn't find your final Lean file within triple angle brackets. "
                "Please output the FULL file for Relations_learned.lean inside <<< and >>>, starting with the required import header."
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            print("⚠️  Warning: missing triple angle bracket block, retrying...")
            continue

        # CHECK 2: Make sure that there is no import statements in the model response
        model_prediction = matches[-1].strip()
        lines = list(model_prediction.splitlines())
        if any(ln.strip().startswith("import ") for ln in lines):
            feedback = (
                "Your Lean file contains import statements. Please remove all import statements and re-output the full file. "
                "Please don't worry about the import statements, they will be added later."
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            print("⚠️  Warning: import statements found, retrying...")
            continue

        # CHECK 3: Lean file syntax validation
        lean_file = f"{header}\n\n\n{previous_extension_files}\n\n\n{model_prediction}"
        error = validator.validate_lean_file(
            lean_file=lean_file,
            instance_name="dsl_extension",
            command_prefix=["lake", "env", "lean"],
        )
        # If no error, return the Lean file
        if error is None:
            print("✅ DSL extension succeeded. Returning the Lean file ...")
            return response_text, reasoning_summary_list, model_prediction
        # Otherwise, provide feedback and retry
        feedback = (
            "Lean validation failed. Please fix the issues and re-output the full file. "
            "Keep in mind which Lean and Mathlib version you are using!!! "
            f"Here is the Lean error message (verbatim):\n\n{error}"
        )
        messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
        print("❌ Lean validation failed, providing feedback and retrying...")

    print("⚠️  Warning: DSL extension did not pass validation within the allowed attempts")
    return "", [], ""


def extend_dsl_all_sequential(
    dataset: str,
    cdg_list: list[dict[str, Any]],
    batch_size: int,
    llm: UnifiedModel,
    num_attempts: int = 5,
    save_log: bool = True,
) -> str:
    # Determine header used by extend_dsl_single_batch for final assembly
    if dataset == "LeanEuclidPlus":
        header = "import SystemE.Theory.Relations"
    elif dataset == "ProofNet-Lean4_proof_hard":
        header = "import Mathlib"
    else:
        raise NotImplementedError(f"Dataset {dataset} not supported yet")

    # Prepare batches
    cdg_batch_list: list[list[dict[str, Any]]] = []
    for i in range(0, len(cdg_list), batch_size):
        cdg_batch_list.append(cdg_list[i : i + batch_size])

    # Progress tracking: keep a single progress bar line by avoiding extra prints and
    # using postfix for per-batch details instead of changing description repeatedly.
    pbar = tqdm(total=len(cdg_batch_list), desc="Extending DSL", unit="batch", position=0, leave=True, dynamic_ncols=True)

    # Accumulate Lean body using a list
    extension_body_list: list[str] = []

    # Simple logs
    log_list: list[dict[str, Any]] = [] if save_log else []

    for index, cdg_batch in enumerate(cdg_batch_list):
        # Generate/extend using current batch
        batch_response_text, batch_reasoning_summary, new_lean_body = extend_dsl_single_batch(
            dataset=dataset,
            cdg_list=cdg_batch,
            previous_extension_files="\n\n\n".join(extension_body_list),
            llm=llm,
            num_attempts=num_attempts,
        )

        # Append the new Lean body to the list
        extension_body_list.append(new_lean_body)

        # Update progress and logs
        pbar.update(1)
        # Update per-batch info without creating a new bar line
        pbar.set_postfix_str(f"batch {index + 1}/{len(cdg_batch_list)} | concepts {len(cdg_batch)}")

        if save_log:
            log_list.append(
                {
                    "batch_index": index + 1,
                    "llm_reasoning": batch_reasoning_summary,
                    "llm_response": batch_response_text,
                    "new_lean_body": new_lean_body,
                }
            )

        # If a batch fails (empty result), continue to next batch without changing state

    pbar.set_postfix_str(f"done | total batches {len(cdg_batch_list)}")
    pbar.close()
    print()

    # Persist logs
    if save_log:
        with open(f"dsl_extension_log_{dataset}.json", "w", encoding="utf-8") as f:
            json.dump(log_list, f, ensure_ascii=False, indent=2)

    # Assemble final Lean file (include header once if available)
    if extension_body_list:
        separator = "\n\n\n"
        if header:
            return f"{header}{separator}{separator.join(extension_body_list)}"
        return separator.join(extension_body_list)

    # Nothing succeeded
    return ""


# ============================================
# STEP 5: Refactor The DSL Extension
# ============================================
def refactor_dsl_extension(
    dataset: str,
    dsl_extension_path: str,
    llm: UnifiedModel,
    num_iterations: int = 1,
    num_attempts: int = 5,
    save_log: bool = True,
) -> str:
    print(f"Refactoring DSL extension from: {dsl_extension_path}")

    # Load the extension file to refactor
    try:
        with open(dsl_extension_path, "r", encoding="utf-8") as f:
            extension_file = f.read().strip()
    except FileNotFoundError:
        print(f"Error: Extension file not found at {dsl_extension_path}")
        return ""

    # Set the Lean project root directory, and
    # load the DSL documentation
    if dataset == "LeanEuclidPlus":
        root_dir = ROOT_DIR_LeanEuclidPlus
        dsl_doc_path = (
            Path(__file__).parent.parent / "LeanEuclidPlus" / "AutoFormalization" / "statement" / "instructions" / "doc_barebone.txt"
        )
        header = "import SystemE.Theory.Relations"
    elif dataset == "ProofNet-Lean4_proof_hard":
        root_dir = ROOT_DIR_PROOFNET
        dsl_doc_path = Path(__file__).parent / "ProofNetHard" / "doc_barebone.txt"
        header = "import Mathlib"
    else:
        raise NotImplementedError(f"Dataset {dataset} not supported yet")

    try:
        with open(dsl_doc_path, "r", encoding="utf-8") as f:
            dsl_doc = f.read().strip()
    except FileNotFoundError:
        print(f"Warning: DSL doc not found at {dsl_doc_path}, using empty DSL doc")
        dsl_doc = ""

    # Add additional specs for the dataset
    additional_specs = ""
    if dataset == "LeanEuclidPlus":
        additional_specs = (
            "## Refactoring Context\n"
            "1. **Background**: The extension file contains new definitions for 2-Dimensional Euclidean Geometry. "
            "The current DSL implements a formal system of 2-Dimensional Euclidean Geometry in Lean 4.\n\n"
            "2. **No External Imports**: The refactored file should not include any import statements. "
            "Only use what is provided in the current DSL and Lean 4 primitives.\n\n"
            "3. **No New Types**: The refactored file should not introduce any new types. "
            "You **MUST** only use the types provided in the current DSL and Lean 4 primitives.\n\n"
            "4. **No Quantifiers**: Maintain the constraint of not using existential (∃) or universal (∀) quantifiers. "
            "All relations and functions should be quantifier-free.\n\n"
            "5. **No Disjunction**: Maintain the constraint of not using disjunction i.e. '∨' in your implementation formula. "
            "6. **Tactic Registration**: Ensure all new relations, functions, abbreviations, and aliases "
            "are registered under the `simp` tactic using `@[simp]`.\n\n"
            "7. **Angle Measures**: Prioritize using the opaque constant '∟' for right angles "
            "rather than explicit values.\n\n"
            "## Refactoring Criteria\n"
            "1. **Remove Duplication and Redundancy**:\n"
            "   - Identify and eliminate duplicate definitions, relations, or functions that express the same concept\n"
            "   - Merge similar implementations that can be unified into a single, more general definition\n"
            "   - Remove redundant helper functions that are only used once and can be inlined\n"
            "   - Consolidate multiple similar patterns into reusable abstractions\n"
            "   - Example 1: the formal relation `between` already implies "
            "that the three points are mutually distinct and are on the same line, "
            "there is no need to explicitly add these extra clauses "
            "when formalizing the relation of a list of points that are collinear and ordered on a line.\n"
            "   - Example 2: for the formal relation `formConvexQuadrilateral`, the `distinctPointsOnLine` clauses and the `sameSide` "
            "clauses can already ensure that "
            "the four points are mutually distinct, they are not collinear, and the adjacent sides intersect, "
            "so there is no need to explicitly add these extra clauses "
            "when formalizing the relation `formConvexQuadrilateral`.\n"
            "   - Example 3: we can direct refer the an angle as `∠ a:b:c`, so there is no need to provide other APIs to refer "
            "to specific angles of a triangle, a polygon, or formed by specific lines.\n"
            "   - Example 4: the relation `pointsDefineTriangle` is redudant, we already have the existing formal relation `formTriangle`.\n"
            "Please **PAY EXTRA ATTENTION** to the examples!!!\n\n"
            "2. **Improve Abstraction Level**:\n"
            "   - Replace overly specific implementations with more general, reusable abstractions\n"
            "   - Identify patterns that can be generalized to work with different types or parameters\n"
            "   - Remove hardcoded values and replace them with parameters or constants\n"
            "   - Ensure abstractions are at the right level - not too specific\n"
            "   - Example 1: `trianglesSimilar` and `trianglesCongruent` are also applicable to degenrated triangles, "
            "so we can make this relation more general by revmoing the extra clauses that requires the two triangles to be non-degenrated. "
            "You should just keep the definition of 'all corresponding angles are equal and all corresponding sides are proportionally equal'.\n"
            "Please **PAY EXTRA ATTENTION** to the examples!!!\n\n"
            "3. **Enhance Consistency and Style**:\n"
            "   - Ensure naming conventions are consistent with the existing DSL\n"
            "   - Standardize parameter ordering and naming patterns\n"
            "   - Align documentation style and level of detail with the DSL documentation\n"
            "   - Use consistent formatting and structure throughout\n\n"
            "4. **Optimize Structure and Organization**:\n"
            "   - Group related definitions together logically\n"
            "   - Order definitions to minimize forward references\n"
            "   - Separate concerns appropriately (types, relations, functions, etc.)\n"
            "   - Remove unnecessary complexity and simplify where possible\n\n"
            "5. **Improve Mathematical Rigor**:\n"
            "   - Ensure all mathematical concepts are precisely defined\n"
            "   - Add missing preconditions or assumptions where needed\n"
            "   - Verify that all relations and functions are well-defined\n"
            "   - Remove any mathematically questionable or ambiguous definitions\n\n"
            "6. **Enhance Reusability**:\n"
            "   - Identify opportunities to create more general, reusable components\n"
            "   - Extract common patterns into helper functions or relations\n"
            "   - Ensure definitions can be easily extended or specialized\n"
            "   - Remove unnecessary coupling between different concepts"
        )
    elif dataset == "ProofNet-Lean4_proof_hard":
        additional_specs = (
            "## Refactoring Context\n"
            "1. **Background**: All concepts are in the context of standard undergraduate mathematics, "
            "including Real Analysis, Complex Analysis, Linear Algebra, "
            "Abstract Algebra, Topology, Number Theory, etc. "
            "You should **KEEP IN MIND** that when trying to find directly formal correspondents "
            "you can leverage **EVERYTHING** in Mathlib and primitives in Lean 4 (NOT other libraries).\n\n"
            "2. **No External Imports**: Please do not add any external imports, you are **ONLY** allowed to use what is provided in Mathlib.\n\n"
            "3. **No New Types**: The refactored file should not introduce any new types. "
            "You **MUST** only use the types provided in the current DSL and Lean 4 primitives.\n\n"
            "4. **Tactic Registration**: Ensure all new relations, functions, abbreviations, and aliases "
            "are registered under the `simp` tactic using `@[simp]`.\n\n"
            "## Refactoring Criteria\n"
            "1. **Remove Duplication and Redundancy**:\n"
            "   - Identify and eliminate duplicate definitions, relations, or functions that express the same concept\n"
            "   - Merge similar implementations that can be unified into a single, more general definition\n"
            "   - Remove redundant helper functions that are only used once and can be inlined\n"
            "   - Consolidate multiple similar patterns into reusable abstractions\n\n"
            "2. **Improve Abstraction Level**:\n"
            "   - Replace overly specific implementations with more general, reusable abstractions\n"
            "   - Identify patterns that can be generalized to work with different types or parameters\n"
            "   - Remove hardcoded values and replace them with parameters or constants\n\n"
            "3. **Enhance Consistency and Style**:\n"
            "   - Ensure naming conventions are consistent with the existing DSL\n"
            "   - Standardize parameter ordering and naming patterns\n"
            "   - Align documentation style and level of detail with the DSL documentation\n"
            "   - Use consistent formatting and structure throughout\n\n"
            "4. **Optimize Structure and Organization**:\n"
            "   - Group related definitions together logically\n"
            "   - Order definitions to minimize forward references\n"
            "   - Separate concerns appropriately (types, relations, functions, etc.)\n"
            "   - Combine multiple sections together if they share the same scope!!!\n"
            "   - Remove **ANY** namespaces!!! Users should be able to use our new definitions directly.\n\n"
            "5. **Improve Mathematical Rigor**:\n"
            "   - Ensure all mathematical concepts are precisely defined\n"
            "   - Add missing preconditions or assumptions where needed\n"
            "   - Verify that all relations and functions are well-defined\n"
            "   - Remove any mathematically questionable or ambiguous definitions\n"
            "   - Don't add **ANY**  lemmas, theorems, examples, etc.!!!\n\n"
            "6. **Enhance Reusability**:\n"
            "   - Identify opportunities to create more general, reusable components\n"
            "   - Extract common patterns into helper functions or relations\n"
            "   - Ensure definitions can be easily extended or specialized\n"
            "   - Remove unnecessary coupling between different concepts"
        )

    # Prepare validator directories
    tmp_dir = os.path.join(root_dir, "tmp", "dsl_refactoring")
    os.makedirs(tmp_dir, exist_ok=True)
    validator = Validator(
        root_dir=root_dir,
        tmp_dir=tmp_dir,
        relations_file="",  # no need, since we only need the method `validate_lean_file`
    )

    # Initialize logging if requested
    log_list: list[dict[str, Any]] = [] if save_log else []
    current_refactored_file: str = extension_file

    # Iteratively refactor for `num_iterations` times
    for i in range(num_iterations):
        print("=" * 80)
        print(f"Extension Refactoring Iteration {i+1}/{num_iterations}...")
        print("=" * 80)

        # Construct the prompt for DSL refactoring
        prompt = DSL_REFACTORING_PROMPT.format(
            additional_specs=additional_specs,
            dsl_doc=dsl_doc,
            extension_file=current_refactored_file,
        )

        # Prepare messages for LLM
        messages: Messages = [{"role": "user", "content": [{"type": "input_text", "text": prompt}]}]

        # Try DSL refactoring with validation feedback loop
        iteration_success = False
        for j in range(num_attempts):
            print(f"Attempting Extension Refactoring (attempt {j+1}/{num_attempts})...")

            # Get response from model
            response_text, _, reasoning_summary_list, _ = llm.get_response(None, messages)

            # Add the assistant response to the context
            messages.append({"role": "assistant", "content": [{"type": "output_text", "text": response_text}]})

            # CHECK 1: The response must be surrounded by triple angle brackets
            pattern = r"<<<(.*?)>>>"
            matches = re.findall(pattern, response_text, re.DOTALL)
            if not matches:
                feedback = (
                    "I couldn't find your refactored Lean file within triple angle brackets. "
                    "Please provide your refactored implementation within **triple angle brackets**: "
                    "<<< your refactored implementation goes here >>>"
                )
                messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
                print("⚠️  Warning: missing triple angle bracket block, retrying...")
                continue

            # CHECK 2: Make sure that there are no import statements in the model response
            model_prediction: str = matches[-1].strip()
            lines = list(model_prediction.splitlines())
            if any(ln.strip().startswith("import ") for ln in lines):
                feedback = (
                    "Your refactored Lean file contains import statements. Please remove all import statements and re-output the full file. "
                    "Please don't worry about the import header, they will be added later."
                )
                messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
                print("⚠️  Warning: import statements found, retrying...")
                continue

            # CHECK 3: Lean file syntax validation
            lean_file = f"{header}\n\n\n{model_prediction}"
            error = validator.validate_lean_file(
                lean_file=lean_file,
                instance_name="dsl_refactoring",
                command_prefix=["lake", "env", "lean"],
            )

            # If no error, update the refactored file and continue to next iteration
            if error is None:
                print("✅ DSL refactoring succeeded for this iteration. Continuing to next iteration...")

                # Log successful refactoring if requested
                if save_log:
                    log_data = {
                        "iteration_number": i + 1,
                        "dsl_extension_path": dsl_extension_path,
                        "dataset": dataset,
                        "llm_reasoning": reasoning_summary_list,
                        "llm_response": response_text,
                        "refactored_lean_file": model_prediction,
                        "attempts_used": j + 1,
                        "success": True,
                    }
                    log_list.append(log_data)

                # Update the refactored file and mark iteration as successful
                current_refactored_file = model_prediction
                iteration_success = True
                break

            # Otherwise, provide feedback and retry
            feedback = (
                "Lean validation failed. Please fix the issues and re-output the full refactored file. "
                "Keep in mind which Lean and Mathlib version you are using!!! "
                f"Here is the Lean error message (verbatim):\n\n{error}"
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            print("❌ Lean validation failed, providing feedback and retrying...")

        # If all attempts failed for this iteration, log the failure
        if not iteration_success:
            print("⚠️  Warning: DSL refactoring did not pass validation within the allowed attempts for this iteration")

            if save_log:
                log_data = {
                    "iteration_number": i + 1,
                    "dsl_extension_path": dsl_extension_path,
                    "dataset": dataset,
                    "total_attempts": num_attempts,
                    "success": False,
                    "final_error": "All attempts failed validation for this iteration",
                }
                log_list.append(log_data)

            # Update the refactored file as empty string and exit the outer loop
            current_refactored_file = ""
            break

    # Save the log
    with open(f"dsl_refactoring_log_{dataset}.json", "w", encoding="utf-8") as f:
        json.dump(log_list, f, ensure_ascii=False, indent=2)
    print(f"Refactoring log saved to dsl_refactoring_log_{dataset}.json")

    return f"{header}\n\n\n{current_refactored_file}"


# ============================================
# STEP 6: Update The DSL Documentation
# ============================================
def update_dsl_documentation(
    dataset: str,
    dsl_extension_path: str,
    llm: UnifiedModel,
    num_attempts: int = 5,
    save_log: bool = True,
) -> str:
    print(f"Updating DSL documentation with extension from: {dsl_extension_path}")

    # Load the extension file(s) to document
    try:
        with open(dsl_extension_path, "r", encoding="utf-8") as f:
            extension_files = f.read().strip()
    except FileNotFoundError:
        print(f"Error: Extension file not found at {dsl_extension_path}")
        return ""

    # Load the current DSL documentation
    if dataset == "LeanEuclidPlus":
        dsl_doc_path = (
            Path(__file__).parent.parent / "LeanEuclidPlus" / "AutoFormalization" / "statement" / "instructions" / "doc_barebone.txt"
        )
    # ProofNet-Lean4_proof_hard doesn't need a doc update in our experiment setting
    elif dataset == "ProofNet-Lean4_proof_hard":
        # ask the user whether to continue with the doc update
        user_input = input("Doc Update is not part of the experiment setting. Do you want to continue with the doc update? (y/n): ")
        if user_input != "y" or user_input != "Y":
            print("Doc update skipped. Exiting...")
            return "Doc update skipped for ProofNet-Lean4_proof_hard"
    else:
        raise NotImplementedError(f"Dataset {dataset} not supported yet")

    try:
        with open(dsl_doc_path, "r", encoding="utf-8") as f:
            dsl_doc = f.read().strip()
    except FileNotFoundError:
        print(f"Warning: DSL doc not found at {dsl_doc_path}, using empty DSL doc")
        dsl_doc = ""

    # Add additional specs for the dataset
    if dataset == "LeanEuclidPlus":
        additional_specs = (
            "## Documentation Update Context\n"
            "1. **Background**: The extension file contains new definitions for 2-Dimensional Euclidean Geometry. "
            "The current DSL implements a formal system of 2-Dimensional Euclidean Geometry in Lean 4.\n\n"
            "2. **Naming Consistency**: Add new concepts correctly to their corresponding namespaces "
            "after the '-- Relations and Axioms for Geometric Sorts --' section. "
            "Some relations like `parallel` can be confusing, since it might be defined in the namespace Line or no namespace at all. "
            "Please **PAY EXTRA ATTENTION** to determine the correct namespace for each relation!!!\n\n"
            "For relations that don't belong to any specific namespace, append them to the '-- Geometric Relations --' section. "
            "Do **NOT** write any new sections. Just simply add or append them to the existing sections!!! "
            "You **MUST** not write any extra comments or sections!!!\n\n"
            "3. **Hide Implementation Details**: This is **EXTREMELY IMPORTANT**!!! "
            "We don't want to expose every definition, function, relation, etc. to the user. "
            "Please hide **as many as possible** helper private functions "
            "and intermediate structures from the user in  new DSL documentation.\n"
            "For example, the functions `betweennessChain`, `hasAtLeastThree`, `noneOnLine`, etc. "
            "are all helper functions, which should **NOT** be documented. "
            "You should only document the most high-level relations likes `twoDistinctLinesIntersectAtPoint`, `sequentiallyAligned`, etc. "
            "Please **PAY EXTRA ATTENTION** to the example!!! You should **NOT** document everything!!!\n\n"
            "4. **Subtlety Clarification**: Please explain **ALL** the subtle requirements, specifications, and constraints "
            "for each formal relation. For example, the relation "
            "`formParallelogram (a b c d : Point) (AB CD AC BD : Line)` has a strict and specific meaning: "
            "'mutually distinct points a, b, d, and c (in clockwise/counterclockwise order i.e. ad is a diagonal) form a parallelogram, "
            "where points a and b are on line AB, points c and d are on line CD, points a and c are on line AC, and points b and d are on line BD. "
            "The lines AB, CD, AC, and BD must be distinct.'\n"
            "It also has a strict requirement on the correspondence and order of the arguments: "
            "'Note that the order and correspondence of arguments a, b, c, d, AB, CD, AC, BD is strictly required i.e. a and b must be on AB, "
            "c and d must be on CD, a and c must be on AC, b and d must be on BD, and they must be passed in the exact order!' "
            "It's **EXTREMELY CRITICAL** to specify the order of vertices i.e. "
            "which one is the diagonal, since that will uniquely determine the parallelogram. "
            "Please **PAY EXTRA ATTENTION** to the example, you **MUST** follow the exact style and content when you document a formal relation, "
            "especially `formConvexQuadrilateral`!!!\n\n"
            "5. **Usage Demo**: For each formal relation, provide a usage example just like in the current DSL documentation. "
            "For example, the doc for the relation `sameSide (a b : Point) (L : Line)` in the namespace Point contains: "
            "'The syntax is `a.sameSide b L`.'\n\n"
        )
    else:
        additional_specs = ""

    # Construct the prompt for DSL documentation update
    prompt = DSL_DOC_UPDATE_PROMPT.format(
        additional_specs=additional_specs,
        dsl_doc=dsl_doc,
        extension_files=extension_files,
    )

    # Prepare messages for LLM
    messages: Messages = [{"role": "user", "content": [{"type": "input_text", "text": prompt}]}]

    # Initialize logging if requested
    log_list: list[dict[str, Any]] = [] if save_log else []

    # Try documentation update with retries
    for i in range(num_attempts):
        print(f"Attempting DSL documentation update (attempt {i+1}/{num_attempts})...")

        # Get response from model
        response_text, _, reasoning_summary_list, _ = llm.get_response(None, messages)

        # DEBUG
        print(response_text)

        # Add the assistant response to the context
        messages.append({"role": "assistant", "content": [{"type": "output_text", "text": response_text}]})

        # CHECK 1: The response must be surrounded by triple angle brackets
        pattern = r"<<<(.*?)>>>"
        matches = re.findall(pattern, response_text, re.DOTALL)
        if not matches:
            feedback = (
                "I couldn't find your updated DSL documentation within triple angle brackets. "
                "Please provide your updated documentation within **triple angle brackets**: "
                "<<< your entire new DSL documentation goes here >>>"
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            print("⚠️  Warning: missing triple angle bracket block, retrying...")
            continue

        # CHECK 2: The updated doc should be longer than the original doc
        model_prediction: str = matches[-1].strip()
        if len(model_prediction) < len(dsl_doc):
            feedback = (
                "The updated documentation appears to be shorter than the original doc. "
                "Please provide a comprehensive update that includes all new elements from the extension files, "
                "while preserving the previous documentation intact. "
            )
            messages.append({"role": "user", "content": [{"type": "input_text", "text": feedback}]})
            print("⚠️  Warning: documentation too short, retrying...")
            continue

        # Success! Return the updated documentation
        print("✅ DSL documentation update succeeded. Returning the updated documentation...")

        # Log successful update if requested
        if save_log:
            log_data = {
                "dsl_extension_path": dsl_extension_path,
                "dataset": dataset,
                "llm_reasoning": reasoning_summary_list,
                "llm_response": response_text,
                "updated_documentation": model_prediction,
                "attempts_used": i + 1,
                "success": True,
            }
            log_list.append(log_data)

            with open(f"dsl_doc_update_log_{dataset}.json", "w", encoding="utf-8") as f:
                json.dump(log_list, f, ensure_ascii=False, indent=2)
            print(f"Documentation update log saved to dsl_doc_update_log_{dataset}.json")

        return model_prediction

    # If all attempts failed, log the failure and return empty string
    print("⚠️  Warning: DSL documentation update failed within the allowed attempts")

    if save_log:
        log_data = {
            "dsl_extension_path": dsl_extension_path,
            "dataset": dataset,
            "total_attempts": num_attempts,
            "success": False,
            "final_error": "All attempts failed",
        }
        log_list.append(log_data)

        with open(f"dsl_doc_update_log_{dataset}.json", "w", encoding="utf-8") as f:
            json.dump(log_list, f, ensure_ascii=False, indent=2)
        print(f"Documentation update log saved to dsl_doc_update_log_{dataset}.json")

    return ""


# ============================================
# Pipe Everything Together
# ============================================
def main() -> None:
    """Main function to test concept extraction on LeanEuclidPlus dataset."""
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--dataset",
        type=str,
        choices=["LeanEuclidPlus", "ProofNet-Lean4_proof_hard"],
        default="LeanEuclidPlus",
        help="Testing dataset",
    )
    args = parser.parse_args()

    # Initialize models
    qwen3 = create_unified_model(
        model_id="qwen/qwen3-235b-a22b-2507",
        base_url="https://openrouter.ai/api/v1",
        max_output_tokens=12_288,
        temperature=0.2,
        provider={"only": ["nebius/fp8"]},
    )
    gpt5 = create_unified_model(
        model_id="gpt-5-2025-08-07",
        base_url="https://api.openai.com/v1",
        max_output_tokens=24_576,
        temperature=1.0,
        verbosity="medium",
        reasoning_effort="high",
        reasoning_summary="detailed",
    )

    # # ============================================
    # # STEP 1: Extract Common Concepts
    # # ============================================
    # # Load statement list
    # statement_list = prepare_statement_list(args.dataset)
    # # Setup the model for different benchmarks
    # if args.dataset == "LeanEuclidPlus":
    #     llm = qwen3
    # elif args.dataset == "ProofNet-Lean4_proof_hard":
    #     llm = gpt5
    # else:
    #     raise NotImplementedError(f"Dataset {args.dataset} not supported yet")
    # # Extract concepts
    # concept_dict = extract_concept_all_sequential(
    #     args.dataset,
    #     statement_list,
    #     batch_size=10,
    #     llm=llm,
    #     num_attempts=5,
    #     save_log=True,
    # )
    # # Save concept dictionary
    # with open(f"concept_dict_{args.dataset}.json", "w", encoding="utf-8") as f:
    #     json.dump(concept_dict, f, ensure_ascii=False, indent=2)
    # print(f"Concept dictionary saved to concept_dict_{args.dataset}.json")

    # # ============================================
    # # STEP 2: Filter Extracted Concepts
    # # ============================================
    # # Load concept dictionary
    # with open(f"concept_dict_{args.dataset}.json", "r", encoding="utf-8") as f:
    #     concept_dict = json.load(f)
    # # Setup the model for different benchmarks
    # if args.dataset == "LeanEuclidPlus":
    #     llm = qwen3
    # elif args.dataset == "ProofNet-Lean4_proof_hard":
    #     llm = gpt5
    # else:
    #     raise NotImplementedError(f"Dataset {args.dataset} not supported yet")
    # # Filter concepts
    # concept_dict_filtered = filter_extracted_concepts(
    #     args.dataset,
    #     concept_dict,
    #     llm=llm,  # qwen3 for LeanEuclidPlus, gpt5 for ProofNet
    #     threshold=0,
    #     num_iterations=5,  # 1 for LeanEuclidPlus, 5 for ProofNet
    #     num_attempts=5,
    #     save_log=True,
    # )
    # # Save filtered concept dictionary
    # with open(f"concept_dict_{args.dataset}_filtered.json", "w", encoding="utf-8") as f:
    #     json.dump(concept_dict_filtered, f, ensure_ascii=False, indent=2)
    # print(f"Filtered concept dictionary saved to concept_dict_{args.dataset}_filtered.json")

    # # ============================================
    # # STEP 3: Construct Concept Dependency Graph (CDG)
    # # ============================================
    # # Load filtered concept dictionary
    # with open(f"concept_dict_{args.dataset}_filtered.json", "r", encoding="utf-8") as f:
    #     concept_dict_filtered = json.load(f)
    # # Setup the model for different benchmarks
    # if args.dataset == "LeanEuclidPlus":
    #     llm = qwen3
    # elif args.dataset == "ProofNet-Lean4_proof_hard":
    #     llm = gpt5
    # else:
    #     raise NotImplementedError(f"Dataset {args.dataset} not supported yet")
    # # Construct CDG
    # concept_list = list(concept_dict_filtered.keys())
    # concept_dependency_graph = construct_cdg_all_sequential(
    #     args.dataset,
    #     concept_list,
    #     batch_size=5,
    #     llm=llm,  # qwen3 for LeanEuclidPlus, gpt5 for ProofNet
    #     num_attempts=5,
    #     save_log=True,
    # )
    # # Save the dependency graph
    # with open(f"cdg_{args.dataset}.json", "w", encoding="utf-8") as f:
    #     json.dump(concept_dependency_graph, f, ensure_ascii=False, indent=2)
    # print(f"Concept Dependency Graph (CDG) saved to cdg_{args.dataset}.json")

    # # ============================================
    # # STEP 4: Extend The DSL
    # # ============================================
    # # Load the CDG
    # with open(f"cdg_{args.dataset}.json", "r", encoding="utf-8") as f:
    #     cdg = json.load(f)
    # # Conver the CDG to a list of dicts, adding the key as a field "concept"
    # cdg_list = [{"concept": concept, **data} for concept, data in cdg.items()]
    # # Setup the model for different benchmarks
    # if args.dataset == "LeanEuclidPlus" or args.dataset == "ProofNet-Lean4_proof_hard":
    #     llm = gpt5
    # else:
    #     raise NotImplementedError(f"Dataset {args.dataset} not supported yet")
    # # Extend the DSL (side-effect only). Keep the return value to avoid unused warnings.
    # lean_file = extend_dsl_all_sequential(
    #     dataset=args.dataset,
    #     cdg_list=cdg_list,
    #     batch_size=5,
    #     llm=llm,
    #     num_attempts=10,
    #     save_log=True,
    # )
    # # Save the Lean file
    # with open("Relations_learned.lean", "w", encoding="utf-8") as f:
    #     f.write(lean_file)
    # print(f"Generated Lean file: {lean_file}")

    # ============================================
    # STEP 5: Refactor The DSL Extension
    # ============================================
    # Setup the model for different benchmarks
    if args.dataset == "LeanEuclidPlus" or args.dataset == "ProofNet-Lean4_proof_hard":
        llm = gpt5
    else:
        raise NotImplementedError(f"Dataset {args.dataset} not supported yet")
    # Refactor the DSL extension file
    refactored_file = refactor_dsl_extension(
        dataset=args.dataset,
        dsl_extension_path="Relations_learned.lean",
        llm=llm,
        num_iterations=1,
        num_attempts=10,
        save_log=True,
    )
    # Save the refactored Lean file
    with open("Relations_learned_refactored.lean", "w", encoding="utf-8") as f:
        f.write(refactored_file)
    print("Refactored file saved to Relations_learned_refactored.lean")

    # ============================================
    # STEP 6: Update The DSL Documentation
    # ============================================
    # Setup the model for different benchmarks
    if args.dataset == "LeanEuclidPlus" or args.dataset == "ProofNet-Lean4_proof_hard":
        llm = gpt5
    else:
        raise NotImplementedError(f"Dataset {args.dataset} not supported yet")
    # Update the DSL documentation
    updated_doc = update_dsl_documentation(
        dataset=args.dataset,
        dsl_extension_path="Relations_learned_refactored.lean",
        llm=llm,
        num_attempts=5,
        save_log=True,
    )
    # Save the updated DSL documentation
    with open("doc_learned.txt", "w", encoding="utf-8") as f:
        f.write(updated_doc)
    print("Updated DSL documentation saved to doc_learned.txt")


if __name__ == "__main__":
    main()
