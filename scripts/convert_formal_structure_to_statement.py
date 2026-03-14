# License: Apache 2.0


# Standard Library Modules
import copy
import re
import os
from typing import Literal

# External Modules
import json5


# ==================== Constants ====================
VALID_CATEGORIES = ["Parallel", "Congruent", "Triangle", "Quadrilateral", "Similarity"]
DEFAULT_NAMESPACE = "Parallel"

THEOREM_TEMPLATE = """import SystemE
import Book
import UniGeo.{relations_file}

open Elements.Book1

namespace UniGeo.{namespace}

theorem theorem_{theorem_suffix} : ∀ {declarations},
  {formatted_premises} →
  {formatted_conclusions} :=
by
{proof_content}

end UniGeo.{namespace}"""

REASONING_FROM_FORMAL_TEMPLATE = (
    "Now we can combine the declarations, premises, and conclusions to convert the Formalized Structure to a Formalized Statement. "
    "According to the guidelines, we will do the following:\n\n"
    "1. Quantify the declared variables correctly.\n"
    "2. Use the conjunction of all formal clauses in the premises as the antecedent.\n"
    "3. Use the conjunction of all formal clauses in the conclusions as the consequent.\n"
    "4. Connect the antecedent and consequent with an implication (→).\n"
    "5. Wrap the entire Formalized Statement with triple angle brackets (<<< Lean expression here >>>) for parsing.\n\n"
    "Finally, we have the Formalized Statement:"
)

REASONING_FROM_SEMI_TEMPLATE = (
    "Now we can convert the Semi-Formalized Structure to a Formalized Statement. "
    "According to the guidelines, we will do the following:\n\n"
    "1. Formalize each clause in the premises, and use the conjunction of them as the antecedent.\n"
    "2. Formalize each clause in the conclusions, and use the conjunction of them as the consequent.\n"
    "3. Connect the antecedent and consequent with an implication (→).\n"
    "4. Declare all geometric objects that is mentioned in the premises or conclusions as variables.\n"
    "5. Quantify the declared variables correctly.\n"
    "6. Wrap the entire Formalized Statement with triple angle brackets (<<< Lean expression here >>>) for parsing.\n\n"
    "Finally, we have the Formalized Statement:"
)


# ==================== Statement Construction ====================
def format_clauses(clauses: list[str], mode: Literal["lean", "text"]) -> str:
    """Format clauses (premises or conclusions) with ∧ operators."""
    # make a deep copy of clauses to avoid modifying the original list
    clauses_copy = copy.deepcopy(clauses)

    # If a clause contains a logical operator inside, we wrap it with parentheses
    for i, clause in enumerate(clauses_copy):
        if " ∧ " in clause or " ∨ " in clause or " → " in clause or " ↔ " in clause:
            # Wrap the clause in parentheses to ensure correct precedence and enhance readability
            clauses_copy[i] = f"({clause})"

    if mode == "lean":
        return " ∧\n  ".join(clauses_copy)
    return " ∧ ".join(clauses_copy)


# ==================== Proof Extraction ====================
def extract_proof_from_original(original_file_path: str) -> str:
    """Extract the proof section from an original Lean formalization file."""
    with open(original_file_path, "r", encoding="utf-8") as f:
        content = f.read()

    # Find the proof section (everything after 'by' until 'end')
    proof_match = re.search(r"by\s+(.*?)\s+end\s+UniGeo\.", content, re.DOTALL)
    if proof_match:
        proof_content = proof_match.group(1).strip()
        return proof_content

    return ""


def extract_variable_declarations(lean_content: str) -> tuple[list[str], list[str]]:
    """Extract point and line variable declarations from Lean theorem content."""
    # Match the theorem declaration pattern
    decl_match = re.search(r"theorem\s+\w+\s*:\s*∀\s*\(([^)]+)\s*:\s*Point\)\s*\(([^)]+)\s*:\s*Line\)", lean_content)

    if decl_match:
        points_str = decl_match.group(1).strip()
        lines_str = decl_match.group(2).strip()

        # Split by spaces and clean up
        points = [p.strip() for p in points_str.split() if p.strip()]
        lines = [line.strip() for line in lines_str.split() if line.strip()]

        return points, lines

    return [], []


def parse_declarations_string(declarations: str) -> tuple[list[str], list[str]]:
    """Parse variable declarations directly from declarations string like '(A B C : Point) (AB BC : Line)'."""
    # Match the declarations pattern: (points : Point) (lines : Line)
    decl_match = re.search(r"\(([^)]+)\s*:\s*Point\)\s*\(([^)]+)\s*:\s*Line\)", declarations)

    if decl_match:
        points_str = decl_match.group(1).strip()
        lines_str = decl_match.group(2).strip()

        # Split by spaces and clean up
        points = [p.strip() for p in points_str.split() if p.strip()]
        lines = [line.strip() for line in lines_str.split() if line.strip()]

        return points, lines

    return [], []


def create_mapping_and_adapt_proof(proof: str, original_lines: list[str], new_lines: list[str]) -> tuple[str, dict[str, str]]:
    """Create variable mapping and adapt proof variables in one step."""
    mapping = {}

    # Points should NEVER be mapped - they stay the same
    # No point mapping at all

    # For lines, only map if they have same endpoints but different order
    for orig_line in original_lines:
        # Find matching line in new formalization
        if orig_line in new_lines:
            # Line name is exactly the same, no mapping needed
            continue

        # Try to find a line with the same endpoints but different order
        orig_points_in_line = list(orig_line)
        for new_line in new_lines:
            new_points_in_line = list(new_line)
            if len(orig_points_in_line) == len(new_points_in_line) and set(orig_points_in_line) == set(new_points_in_line):
                # Same endpoints, different order - create mapping
                mapping[orig_line] = new_line
                break

    # Adapt proof variables using the mapping
    adapted_proof = proof
    for orig_var, new_var in mapping.items():
        if orig_var != new_var:
            # Use word boundaries to ensure we only replace complete variable names
            pattern = r"\b" + re.escape(orig_var) + r"\b"
            adapted_proof = re.sub(pattern, new_var, adapted_proof)

    return adapted_proof, mapping


def extract_and_adapt_proof(original_file_path: str, declarations: str) -> str:
    """Extract proof from original file and adapt it to match new variable names in provided declarations."""
    # Read original file
    with open(original_file_path, "r", encoding="utf-8") as f:
        original_content = f.read()

    # Extract proof from original
    proof = extract_proof_from_original(original_file_path)
    if not proof:
        raise ValueError(f"Could not extract proof from {original_file_path}")

    # Extract variable declarations from original content
    orig_points, orig_lines = extract_variable_declarations(original_content)

    # Parse variable declarations from new declarations string
    new_points, new_lines = parse_declarations_string(declarations)

    if not orig_points or not new_points:
        raise ValueError("Could not extract variable declarations from original content or new declarations")

    # Create variable mapping and adapt proof
    adapted_proof, variable_mapping = create_mapping_and_adapt_proof(proof, orig_lines, new_lines)

    print(f"📋 Variable mapping: {variable_mapping}")

    # Ensure all lines have at least 2 spaces of indentation (base level under 'by')
    proof_lines = adapted_proof.split("\n")
    indented_proof_lines = []
    for line in proof_lines:
        if line.strip():  # Non-empty line
            if line.startswith("  "):
                # Already properly indented, keep as is
                indented_proof_lines.append(line)
            else:
                # Add base indentation
                indented_proof_lines.append("  " + line.lstrip())
        else:
            # Empty line, keep as is
            indented_proof_lines.append(line)
    proof_content = "\n".join(indented_proof_lines)

    return proof_content


# ==================== JSON5 to Lean & Text ====================
def determine_namespace_from_path(json5_file_path: str) -> str:
    """Determine the appropriate namespace based on directory structure."""
    # Extract the category from the path
    # Expected structure: .../UniGeo/Category/formalized_structures/x.json5
    path_parts = json5_file_path.split(os.sep)

    # Find the parent directory of formalized_structures
    try:
        formalized_idx = path_parts.index("formalized_structures")
        if formalized_idx > 0:
            category = path_parts[formalized_idx - 1]
            # Validate it's one of the expected categories
            if category in VALID_CATEGORIES:
                return category
    except (ValueError, IndexError):
        pass

    # Default fallback
    print(f"⚠️  Warning: Could not determine namespace for {json5_file_path}. Defaulting to '{DEFAULT_NAMESPACE}'.")
    return DEFAULT_NAMESPACE


def generate_theorem_lean_file(
    relations_file: str,
    theorem_suffix: str,
    declarations: str,
    premises: list[str],
    conclusions: list[str],
    namespace: str,
    original_file_path: str,
) -> str:
    """Generate complete Lean theorem statement with proof extraction from original file."""

    # Check if original formalization file exists
    if not os.path.exists(original_file_path):
        raise FileNotFoundError(f"Original file not found: {original_file_path}")

    # Format the premises and conclusions
    formatted_premises = format_clauses(premises, mode="lean")
    formatted_conclusions = format_clauses(conclusions, mode="lean")

    print(f"🔍 Extracting proof from: {original_file_path}")
    proof_content = extract_and_adapt_proof(original_file_path, declarations)

    theorem_lean_file = THEOREM_TEMPLATE.format(
        relations_file=relations_file,
        namespace=namespace,
        theorem_suffix=theorem_suffix,
        declarations=declarations,
        formatted_premises=formatted_premises,
        formatted_conclusions=formatted_conclusions,
        proof_content=proof_content,
    )

    return theorem_lean_file


def generate_theorem_text_cot_files(
    declarations: str,
    premises: list[str],
    conclusions: list[str],
) -> tuple[str, str]:
    """Generate text representation of the theorem with Chain-of-Thought (CoT) style reasoning."""

    # Format the premises and conclusions
    formatted_premises = format_clauses(premises, mode="text")
    formatted_conclusions = format_clauses(conclusions, mode="text")

    # Create the theorem text
    theorem_text = f"<<< ∀ {declarations}, {formatted_premises} → {formatted_conclusions} >>>"

    # Add CoT style reasoning
    theorem_text_file_from_formal = f"{REASONING_FROM_FORMAL_TEMPLATE}\n\n{theorem_text}"
    theorem_text_file_from_semi = f"{REASONING_FROM_SEMI_TEMPLATE}\n\n{theorem_text}"

    return theorem_text_file_from_formal, theorem_text_file_from_semi


# -------------------- Helper Functions --------------------
def process_formalized_structure(
    json5_file_path: str,
    output_file_path: str,
    theorem_num: str,
    declarations: str,
    namespace: str,
    original_file_path: str,
    suffix: str = "",
    relations_file: str = "Relations",
    text_suffix: str = "",
) -> None:
    """Process a single formalized structure file and generate Lean and text files."""

    # Read JSON5 file
    with open(json5_file_path, "r", encoding="utf-8") as f:
        data = json5.load(f)

    premises = data["premises"]
    conclusions = data["conclusions"]

    # Generate the complete Lean theorem with proof extraction handled internally
    theorem_suffix = f"{theorem_num}{suffix}" if suffix else theorem_num
    theorem_lean_file = generate_theorem_lean_file(relations_file, theorem_suffix, declarations, premises, conclusions, namespace, original_file_path)

    # Write the complete file once
    lean_filename = f"Example0{theorem_num}.lean"
    lean_output_file_path = output_file_path.replace(f"{theorem_num}.lean", lean_filename)
    # Create output file dirs
    os.makedirs(os.path.dirname(lean_output_file_path), exist_ok=True)
    # Write the Lean file
    with open(lean_output_file_path, "w", encoding="utf-8") as f:
        f.write(theorem_lean_file)

    print(f"✅ Converted {json5_file_path} → {lean_output_file_path} (namespace: {namespace})")

    # Generate text representation of the theorem with CoT style reasoning
    theorem_text_from_formal, theorem_text_from_semi = generate_theorem_text_cot_files(declarations, premises, conclusions)

    # Create output file paths for text files
    if text_suffix and text_suffix in output_file_path:
        # For barebone and oracle variants where the suffix is already in the path
        text_file_from_formal = output_file_path.replace("formalizations", "formalized_texts_from_formal").replace(".lean", ".txt")
        text_file_from_semi = output_file_path.replace("formalizations", "formalized_texts_from_semi").replace(".lean", ".txt")
    elif text_suffix:
        # For barebone and oracle variants where we need to add the suffix
        text_file_from_formal = output_file_path.replace("formalizations", f"formalized_texts_from_formal{text_suffix}").replace(".lean", ".txt")
        text_file_from_semi = output_file_path.replace("formalizations", f"formalized_texts_from_semi{text_suffix}").replace(".lean", ".txt")
    else:
        # For regular variants, use the standard directory structure
        text_file_from_formal = output_file_path.replace("formalizations", "formalized_texts_from_formal").replace(".lean", ".txt")
        text_file_from_semi = output_file_path.replace("formalizations", "formalized_texts_from_semi").replace(".lean", ".txt")

    # Create output file dirs
    os.makedirs(os.path.dirname(text_file_from_formal), exist_ok=True)
    os.makedirs(os.path.dirname(text_file_from_semi), exist_ok=True)

    # Write the text files
    with open(text_file_from_formal, "w", encoding="utf-8") as f:
        f.write(theorem_text_from_formal)
    print(f"✅ Generated text file: {text_file_from_formal} (namespace: {namespace})")

    with open(text_file_from_semi, "w", encoding="utf-8") as f:
        f.write(theorem_text_from_semi)
    print(f"✅ Generated text file: {text_file_from_semi} (namespace: {namespace})")


# -------------------- Single JSON5 Processing --------------------
def convert_json5_to_lean_and_text(json5_file_path: str, output_file_path: str) -> None:
    """Convert a single JSON5 file to 1 Lean theorem file and 2 text files with CoT style reasoning."""

    # Extract theorem number from json5 filename
    json5_filename = os.path.basename(json5_file_path)
    theorem_num: str = json5_filename.split(".")[0]

    # Check if the file name is valid, skip if not a number
    if not theorem_num.isdigit():
        print(f"⚠️  Warning: Invalid filename {json5_filename}. Skipping...")
        return

    # Determine namespace from directory structure
    namespace = determine_namespace_from_path(json5_file_path)

    # Read declarations from pre-written txt file
    declarations_file_path = json5_file_path.replace("formalized_structures", "declarations_from_formal").replace(".json5", ".txt")
    with open(declarations_file_path, "r", encoding="utf-8") as f:
        # Last non-empty line is expected to contain the declarations
        declarations = f.read().strip().splitlines()[-1]

    # Get original formalization path for proof extraction
    original_file_path = json5_file_path.replace("formalized_structures", "original_formalizations").replace(".json5", ".lean")

    # If exists, convert the json5 formal structure in oracle DSL to Lean
    oracle_file_path = json5_file_path.replace("formalized_structures", "formalized_structures_oracle")
    if os.path.exists(oracle_file_path):
        # Process the oracle DSL structure
        oracle_output_path = output_file_path.replace("formalizations", "formalizations_oracle")
        process_formalized_structure(
            oracle_file_path,
            oracle_output_path,
            theorem_num,
            declarations,
            namespace,
            original_file_path,
            suffix="_oracle",
            relations_file="Relations_oracle",
            text_suffix="_oracle",
        )

    # If exists, convert the json5 formal structure in barebone DSL to Lean
    barebone_file_path = json5_file_path.replace("formalized_structures", "formalized_structures_barebone")
    if os.path.exists(barebone_file_path):
        # Process the barebone DSL structure
        barebone_output_path = output_file_path.replace("formalizations", "formalizations_barebone")
        process_formalized_structure(
            barebone_file_path,
            barebone_output_path,
            theorem_num,
            declarations,
            namespace,
            original_file_path,
            suffix="_barebone",
            relations_file="Relations_barebone",
            text_suffix="_barebone",
        )

    # If exists, convert the json5 formal structure in learned DSL to Lean
    learned_file_path = json5_file_path.replace("formalized_structures", "formalized_structures_learned")
    if os.path.exists(learned_file_path):
        # Process the learned DSL structure
        learned_output_path = output_file_path.replace("formalizations", "formalizations_learned")
        process_formalized_structure(
            learned_file_path,
            learned_output_path,
            theorem_num,
            declarations,
            namespace,
            original_file_path,
            suffix="_learned",
            relations_file="Relations_learned",
            text_suffix="_learned",
        )


# -------------------- Batch JSON5 Processing --------------------
def convert_all_files(input_dir: str, output_dir: str) -> None:
    """Convert all JSON5 files in input directory to Lean files in output directory."""

    # Ensure output directory exists
    os.makedirs(output_dir, exist_ok=True)

    # Find all JSON5 files
    if not os.path.exists(input_dir):
        print(f"⚠️  Warning: Input directory {input_dir} does not exist. Skipping...")
        return

    json5_files = [f for f in os.listdir(input_dir) if f.endswith(".json5")]
    json5_files.sort()  # Process in order

    if not json5_files:
        print(f"No JSON5 files found in {input_dir}")
        return

    for json5_file in json5_files:
        input_path = os.path.join(input_dir, json5_file)

        # Generate output filename
        output_file = json5_file.replace(".json5", ".lean")
        output_path = os.path.join(output_dir, output_file)

        print("-" * 60)
        convert_json5_to_lean_and_text(input_path, output_path)


def main() -> None:
    """Main function to run the converter."""
    # Process all valid categories
    for category in VALID_CATEGORIES:
        input_dir = f"../LeanEuclidPlus/Examples/UniGeo/{category}/formalized_structures"
        output_dir = f"../LeanEuclidPlus/Examples/UniGeo/{category}/formalizations"

        print("=" * 100)
        print(f"🔨 Converting formalized structures in {category} to Lean theorems...")
        convert_all_files(input_dir, output_dir)
        print(f"Conversion for {category} complete!")
        print("=" * 100)


if __name__ == "__main__":
    main()
