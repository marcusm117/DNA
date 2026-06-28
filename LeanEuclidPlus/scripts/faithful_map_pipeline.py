#!/usr/bin/env python3
"""
3-stage faithful-map pipeline.

Stage 1: Split English text into atomic claims (text-only LLM, no Lean/diagram).
Stage 2: Translate claims to Lean types (LLM with diagram + vocab, no codebase).
Stage 3: Assemble Main.lean deterministically (no LLM).

Usage:
  python3 scripts/faithful_map_pipeline.py Book2/Prop11 --stage1
  python3 scripts/faithful_map_pipeline.py Book2/Prop11 --stage2 --stage1-json stage1.json
  python3 scripts/faithful_map_pipeline.py Book2/Prop11 --stage3 --stage2-json stage2.json
  python3 scripts/faithful_map_pipeline.py Book2/Prop11 --all   # full pipeline with pauses
"""

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent

# ---------------------------------------------------------------------------
# Stage 1: Split + Mark
# ---------------------------------------------------------------------------

STAGE1_SYSTEM_PROMPT = """\
You are a text analyst for ancient Greek mathematical proofs (Euclid's Elements, Fitzpatrick \
translation). Your ONLY job is to split a proof text into atomic assertions and mark their roles.

You know NOTHING about Lean, formal logic, or any programming language. You work purely with \
English text structure.

## Rules

1. **VERBATIM TILING**: Your output slices, joined by single spaces in index order, must reproduce \
the ENTIRE input text CHARACTER-FOR-CHARACTER. Nothing reworded, dropped, duplicated, or reordered.

2. **ONE ATOMIC CLAIM PER ENTRY**: Each entry asserts ONE thing (one equality, one angle fact, one \
figure property, one construction action). If a sentence packs multiple claims ("$CB$ is equal to \
$GK$, and $CG$ to $KB$"), SPLIT it into separate entries at a clause boundary — but ONLY if the \
split produces clean contiguous slices that tile. If not (interleaved facts), keep as one entry.

3. **NEVER MERGE ACROSS SENTENCES**: A period/full-stop boundary is ALWAYS at least an entry \
boundary. Two sentences never become one entry.

4. **TRAILING JUSTIFICATIONS STAY**: A "For..." or "since..." clause that gives the REASON for a \
claim stays in the same entry as its claim — it's the justification, not a new assertion.

5. **SPLIT-ONLY**: You may split a sentence into multiple entries, but never merge.

## Roles

- **intro**: The opening block: enunciation ("If...then...") + "For let..." setup + "I say that..." \
  This is ALWAYS entry index 0. It runs from the start up to and including the "I say that..." \
  sentence. Everything before the first construction/deduction is intro.

- **construction**: "Let X be drawn/described/joined/produced..." — an action that creates a new \
  geometric object. Mark what proposition is cited (if any) and what objects are introduced.

- **deduction**: An assertion about a relationship or equality between geometric objects. \
  This is the bulk of the proof. Identify:
  - The ASSERTION: what the entry claims (in plain English).
  - JUSTIFICATIONS: any "since X", "for X", "X being equal to Y" clauses that cite a prior fact \
    as the REASON for this assertion. Each justification must be a VERBATIM CONTIGUOUS SUBSTRING \
    of the entry's text. Only mark substrings that cite a PRIOR fact consumed by this step — \
    NOT the assertion itself.

- **conclusion**: The final "Thus, if...then... (Which is) the very thing it was required to show." \
  This is ALWAYS the last entry. It restates the theorem and closes with QED.

## Output format

Return a JSON array. Each element:
{
  "index": <int>,           // 0-based position
  "role": "intro"|"construction"|"deduction"|"conclusion",
  "text": "<verbatim slice>",

  // For constructions:
  "construction_cite": "<book>.<prop>" or null,  // e.g. "1.46", "1.31"
  "objects_introduced": ["$X$", "$YZ$"],         // Euclid labels of new objects

  // For deductions:
  "assertion": "<plain English paraphrase of what is claimed>",
  "justifications": [
    {"substring": "<verbatim contiguous substring of text>", "kind": "prior_fact"}
  ],
  "proof_cite": "<book>.<prop>" or null  // if [Prop.~B.N] appears
}

Fields not relevant to a role should be omitted (not null).
"""

STAGE1_USER_TEMPLATE = """\
Split the following Euclid proof text into atomic assertions. Follow the rules exactly.

TEXT:
{text}
"""


def run_stage1(text: str, *, model: str = "claude-sonnet-4-6-20250514", dry_run: bool = False) -> list:
    """Call the Anthropic API for Stage 1 (text splitting)."""
    if dry_run:
        print("[DRY RUN] Would call API with Stage 1 prompt")
        print(f"  Text length: {len(text)} chars")
        return []

    try:
        import anthropic
    except ImportError:
        sys.exit("ERROR: `anthropic` package not installed. Run: pip install anthropic")

    import os
    if not os.environ.get("ANTHROPIC_API_KEY"):
        sys.exit("ERROR: ANTHROPIC_API_KEY environment variable not set.")

    client = anthropic.Anthropic()
    message = client.messages.create(
        model=model,
        max_tokens=8192,
        system=STAGE1_SYSTEM_PROMPT,
        messages=[
            {"role": "user", "content": STAGE1_USER_TEMPLATE.format(text=text)}
        ],
    )

    response_text = message.content[0].text
    # Extract JSON from response (handle possible markdown wrapping)
    if "```json" in response_text:
        response_text = response_text.split("```json")[1].split("```")[0]
    elif "```" in response_text:
        response_text = response_text.split("```")[1].split("```")[0]

    result = json.loads(response_text)
    return result


def validate_stage1(sentences: list, original_text: str) -> list[str]:
    """Validate Stage 1 output against the original text. Returns list of errors."""
    errors = []

    if not sentences:
        errors.append("Empty output")
        return errors

    # Check verbatim tiling
    reconstructed = " ".join(s["text"] for s in sentences)
    if reconstructed != original_text:
        errors.append("TILING FAILURE: reconstructed text does not match original")
        # Find first divergence point
        for i, (a, b) in enumerate(zip(reconstructed, original_text)):
            if a != b:
                errors.append(f"  First divergence at char {i}: got '{reconstructed[max(0,i-20):i+20]}' vs expected '{original_text[max(0,i-20):i+20]}'")
                break
        if len(reconstructed) != len(original_text):
            errors.append(f"  Length mismatch: got {len(reconstructed)}, expected {len(original_text)}")

    # Check indices are sequential
    indices = [s["index"] for s in sentences]
    if indices != list(range(len(sentences))):
        errors.append(f"Indices not sequential 0..{len(sentences)-1}: {indices}")

    # Check first is intro, last is conclusion
    if sentences[0]["role"] != "intro":
        errors.append(f"First entry role is '{sentences[0]['role']}', expected 'intro'")
    if sentences[-1]["role"] != "conclusion":
        errors.append(f"Last entry role is '{sentences[-1]['role']}', expected 'conclusion'")

    # Check justification substrings are verbatim
    for s in sentences:
        if "justifications" in s:
            for j in s["justifications"]:
                if j["substring"] not in s["text"]:
                    errors.append(
                        f"  Entry {s['index']}: justification substring not found in text: "
                        f"'{j['substring']}'"
                    )

    # Check no merge across sentence boundaries (period followed by space+capital)
    for s in sentences:
        # Count sentence-ending periods (not abbreviations like "Prop.")
        text = s["text"]
        # Simple heuristic: ". " followed by uppercase (but not after "Prop." or similar)
        import re
        # Sentences end with period+space+uppercase, excluding "Prop.~" and "[Prop.~"
        potential_boundaries = list(re.finditer(r'(?<!Prop)(?<!~)\. [A-Z]', text))
        if s["role"] not in ("intro", "conclusion") and len(potential_boundaries) > 1:
            # Multiple sentence boundaries in a non-intro/conclusion entry — warn
            errors.append(
                f"  Entry {s['index']} ({s['role']}): may contain multiple sentences "
                f"({len(potential_boundaries)} boundaries found). Consider splitting."
            )

    return errors


# ---------------------------------------------------------------------------
# Stage 2: Translate (TODO)
# ---------------------------------------------------------------------------

VOCAB_SHEET_PATH = SCRIPT_DIR / "faithful_map_vocab.md"


def run_stage2(stage1_json: list, diagram_path: Path, prop_signature: str,
               *, model: str = "claude-opus-4-6-20250514", dry_run: bool = False) -> list:
    """Call the Anthropic API for Stage 2 (translation to Lean)."""
    raise NotImplementedError("Stage 2 not yet implemented")


# ---------------------------------------------------------------------------
# Stage 3: Assemble (TODO)
# ---------------------------------------------------------------------------

def run_stage3(stage2_json: list, main_path: Path) -> str:
    """Deterministically assemble Main.lean from Stage 2 output."""
    raise NotImplementedError("Stage 3 not yet implemented")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def resolve_prop_paths(propdir: str):
    """Resolve paths for a proposition directory."""
    # propdir like "Book2/Prop11"
    parts = propdir.split("/")
    if len(parts) != 2:
        sys.exit(f"Expected Book<N>/PropNN, got: {propdir}")

    book_dir = parts[0]  # "Book2"
    prop_name = parts[1]  # "Prop11"

    # Extract book and prop numbers
    book_num = int(book_dir.replace("Book", ""))
    prop_num = int(prop_name.replace("Prop", ""))

    base = REPO_ROOT / book_dir
    text_path = base / "data" / "texts_proofs" / f"{prop_num}.txt"
    diagram_path = base / "data" / "diagrams" / f"{prop_num}.png"
    main_path = base / prop_name / "Main.lean"

    return {
        "book": book_num,
        "prop": prop_num,
        "text_path": text_path,
        "diagram_path": diagram_path,
        "main_path": main_path,
        "propdir": propdir,
    }


def main():
    parser = argparse.ArgumentParser(description="3-stage faithful-map pipeline")
    parser.add_argument("propdir", help="Proposition directory, e.g. Book2/Prop11")
    parser.add_argument("--stage1", action="store_true", help="Run Stage 1 only")
    parser.add_argument("--stage2", action="store_true", help="Run Stage 2 only")
    parser.add_argument("--stage3", action="store_true", help="Run Stage 3 only")
    parser.add_argument("--all", action="store_true", help="Run full pipeline")
    parser.add_argument("--stage1-json", type=str, help="Path to Stage 1 JSON output (for --stage2)")
    parser.add_argument("--stage2-json", type=str, help="Path to Stage 2 JSON output (for --stage3)")
    parser.add_argument("--model", type=str, default=None, help="Override model for LLM calls")
    parser.add_argument("--dry-run", action="store_true", help="Print prompts without calling API")
    parser.add_argument("--output", "-o", type=str, help="Output file for JSON result")

    args = parser.parse_args()

    if not any([args.stage1, args.stage2, args.stage3, args.all]):
        parser.error("Specify --stage1, --stage2, --stage3, or --all")

    paths = resolve_prop_paths(args.propdir)

    if args.stage1 or args.all:
        # Read text
        if not paths["text_path"].exists():
            sys.exit(f"Text file not found: {paths['text_path']}")
        text = paths["text_path"].read_text().strip()

        print(f"=== Stage 1: Split + Mark ===")
        print(f"Text: {paths['text_path']} ({len(text)} chars)")
        print()

        model = args.model or "claude-sonnet-4-6-20250514"
        result = run_stage1(text, model=model, dry_run=args.dry_run)

        if not args.dry_run:
            # Validate
            errors = validate_stage1(result, text)
            if errors:
                print("VALIDATION ERRORS:")
                for e in errors:
                    print(f"  {e}")
                print()

            # Print summary
            print(f"Split into {len(result)} entries:")
            for s in result:
                role_tag = s["role"].upper()
                text_preview = s["text"][:80] + ("..." if len(s["text"]) > 80 else "")
                extra = ""
                if s.get("construction_cite"):
                    extra = f" [Prop.~{s['construction_cite']}]"
                if s.get("justifications"):
                    n = len(s["justifications"])
                    extra += f" ({n} justification{'s' if n > 1 else ''})"
                print(f"  [{s['index']:2d}] {role_tag:14s} {text_preview}{extra}")
            print()

            # Save output
            out_path = args.output or f"stage1_{paths['propdir'].replace('/', '_')}.json"
            with open(out_path, "w") as f:
                json.dump(result, f, indent=2)
            print(f"Saved to: {out_path}")

            if errors:
                print("\n⚠ Fix validation errors before proceeding to Stage 2.")
                sys.exit(1)
            else:
                print("\n✓ Validation passed. Review splits, then proceed to Stage 2.")

    if args.stage2 or (args.all and not args.stage1):
        print("Stage 2 not yet implemented.")
        sys.exit(0)

    if args.stage3 or (args.all and not args.stage1 and not args.stage2):
        print("Stage 3 not yet implemented.")
        sys.exit(0)


if __name__ == "__main__":
    main()
