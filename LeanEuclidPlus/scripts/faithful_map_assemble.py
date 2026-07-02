#!/usr/bin/env python3
"""
Stage 3 of the faithful-map pipeline: deterministic assembly of Main.lean from translate.json.

Usage:
  python3 scripts/faithful_map_assemble.py Book2/Prop11

Reads: Book2/Prop11/split.json   (authoritative sentence TEXT — the --split-verified source of truth)
     + Book2/Prop11/translate.json (claims / constructions / assumptions)
     + existing Main.lean          (for theorem signature)
Writes: Book2/Prop11/Main.lean (overwrites the proof body, preserves signature)

TEXT flows deterministically: split.json (gated by `check_faithful.py --split`) → Main, verbatim.
translate.json's `text` field is NOT used (the translate LLM may have re-typed it) — only its claims.
So Main tiles the canonical text by construction; no downstream stage ever hand-fixes whitespace.
"""

import argparse
import json
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent


def extract_signature(main_text: str) -> tuple[str, str, str]:
    """Extract the theorem signature from Main.lean.

    Returns (pre_signature, signature, post_signature_marker).
    pre_signature = everything up to and including the `theorem` line's `:= by`
    signature = the theorem declaration
    """
    # Find the theorem line and its := by
    # Pattern: everything up to `:= by\n` or `:=\nby`
    m = re.search(
        r'(set_option systemE\.solverTime \d+ in\n)?'
        r'(theorem proposition_\d+[^:]*:.*?:=\s*)\n?\s*by\b',
        main_text, re.DOTALL
    )
    if not m:
        sys.exit("ERROR: Could not find 'theorem proposition_N ... := by' in Main.lean")

    # Everything before the theorem (imports, namespace, etc.)
    theorem_start = m.start()
    return main_text[:theorem_start], m.group(0), main_text[m.end():]


def extract_imports_and_header(main_text: str) -> tuple[str, str]:
    """Split Main.lean into header (imports/options/namespace) and the rest."""
    lines = main_text.split('\n')
    header_end = 0
    for i, line in enumerate(lines):
        if line.startswith('theorem ') or line.startswith('set_option systemE.solverTime'):
            header_end = i
            break
    header = '\n'.join(lines[:header_end])
    return header, '\n'.join(lines[header_end:])


def build_imports(translate_json: list) -> list[str]:
    """Determine required imports from construction citations."""
    imports = ["import SystemE"]
    seen_props = set()

    for entry in translate_json:
        if entry.get("construction") and entry["construction"].get("calls"):
            for call in entry["construction"]["calls"]:
                call_str = call["call"]
                # Extract proposition name
                m = re.match(r'(proposition_\d+)', call_str)
                if m:
                    prop_name = m.group(1)
                    prop_num = int(prop_name.replace("proposition_", ""))
                    if prop_num not in seen_props:
                        seen_props.add(prop_num)
                        # Book 1 props are in Book/, Book 2 in Book2/
                        # Construction props are almost always Book 1
                        imports.append(f"import Book.Prop{prop_num:02d}")

    return imports


def format_assumption_annotation(assumption: dict) -> str:
    """Format a single @assumption annotation line."""
    substring = assumption["substring"]
    lean_type = assumption["lean_type"]
    override = assumption.get("use_override", "")
    if override:
        return f'  -- @assumption ("{substring}", {lean_type}, use_override {override})'
    return f'  -- @assumption ("{substring}", {lean_type})'


def format_construction_calls(construction: dict) -> list[str]:
    """Format construction euclid_apply lines."""
    lines = []
    for call in construction.get("calls", []):
        call_str = call["call"]
        as_str = call["as"]
        # Multi-output: check if as_str contains comma (tuple destructuring)
        if "," in as_str:
            lines.append(f"  euclid_apply ({call_str}) as ({as_str})")
        else:
            lines.append(f"  euclid_apply ({call_str}) as {as_str}")
    return lines


def assemble_main(translate_json: list, split_text: dict, main_path: Path, book: int, prop: int) -> str:
    """Assemble the complete Main.lean.

    TEXT (sentence strings) comes from `split_text` — the `--split`-VERIFIED split.json, the single
    source of truth for the verbatim text (incl. whitespace). We do NOT use translate.json's `text`
    (the translate LLM re-typed it and could have corrupted whitespace). CLAIMS/constructions/
    assumptions come from translate.json. This makes Main tile the canonical text by construction, so
    no downstream stage ever hand-fixes whitespace."""
    main_text = main_path.read_text()

    def text_for(idx):
        if idx not in split_text:
            sys.exit(f"ERROR: split.json has no entry index {idx} — split.json/translate.json are out "
                     f"of sync. Re-run /faithful-split then /faithful-translate.")
        return split_text[idx]

    # Extract existing signature (everything up to and including `:= by`)
    # We need to preserve the theorem signature byte-for-byte
    lines = main_text.split('\n')

    # Find theorem start (with optional cap line before it)
    theorem_start_idx = None
    cap_line_idx = None
    for i, line in enumerate(lines):
        if re.match(r'^set_option systemE\.solverTime \d+ in$', line):
            cap_line_idx = i
        if line.startswith('theorem proposition_'):
            theorem_start_idx = i
            break

    if theorem_start_idx is None:
        sys.exit("ERROR: Could not find 'theorem proposition_N' in Main.lean")

    # Find the `:= by` or `:=\nby` that ends the signature
    sig_end_idx = None
    for i in range(theorem_start_idx, len(lines)):
        if ':= by' in lines[i] or lines[i].strip() == 'by':
            sig_end_idx = i
            break
        if ':=' in lines[i] and i + 1 < len(lines) and lines[i + 1].strip() == 'by':
            sig_end_idx = i + 1
            break

    if sig_end_idx is None:
        sys.exit("ERROR: Could not find ':= by' after theorem signature")

    # Build header (imports + options + namespace)
    imports = build_imports(translate_json)
    has_book1_imports = any(i.startswith("import Book.") for i in imports)
    header_lines = imports + [
        "set_option linter.unusedVariables false",
        "set_option linter.unnecessarySeqFocus false",
        "",
        f"namespace Elements.Book{book}",
    ]
    if book == 2 and has_book1_imports:
        header_lines.append("")
        header_lines.append("open Elements.Book1")

    # Preserve the theorem signature lines
    if cap_line_idx is not None and cap_line_idx == theorem_start_idx - 1:
        sig_lines = lines[cap_line_idx:sig_end_idx + 1]
    else:
        sig_lines = [f"set_option systemE.solverTime 30 in"] + lines[theorem_start_idx:sig_end_idx + 1]

    # Find the namespace end
    namespace_end = f"end Elements.Book{book}"

    # Build the proof body
    body_lines = ["  euclid_intros"]

    # Separate entries by role
    intro_entry = None
    conclusion_entry = None
    step_entries = []

    for entry in translate_json:
        if entry["role"] == "intro":
            intro_entry = entry
        elif entry["role"] == "conclusion":
            conclusion_entry = entry
        else:
            step_entries.append(entry)

    if intro_entry is None:
        sys.exit("ERROR: No intro entry in translate.json")
    if conclusion_entry is None:
        sys.exit("ERROR: No conclusion entry in translate.json")

    # Emit intro sentence
    loc = f"{book}.{prop}.0"
    body_lines.append(f'  euclid_intro_sentence "{loc}"')
    body_lines.append(f'    "{text_for(intro_entry.get("index", 0))}"')
    body_lines.append("")

    # Emit each step
    last_step_name = None
    for entry in step_entries:
        step_name = entry["step_name"]
        step_idx = int(step_name.replace("step", ""))
        loc = f"{book}.{prop}.{step_idx}"
        last_step_name = step_name

        # Construction calls go before the sentence
        if entry.get("construction") and entry["construction"].get("calls"):
            for line in format_construction_calls(entry["construction"]):
                body_lines.append(line)

        # Assumption annotations
        for assumption in entry.get("assumptions", []):
            body_lines.append(format_assumption_annotation(assumption))

        # The euclid_sentence itself (TEXT from split.json, CLAIM from translate.json)
        claim = entry["lean_claim"]
        body_lines.append(f'  euclid_sentence "{loc}"')
        body_lines.append(f'    "{text_for(entry.get("index", step_idx))}"')
        body_lines.append(f'    ({step_name} : {claim}) := by sorry')
        body_lines.append("")

    # Emit the closing
    # Detect existential conclusion (the step claim won't match the ∃ goal directly)
    is_existential = '∃' in main_text[:main_text.find(':= by') if ':= by' in main_text else len(main_text)]
    if last_step_name:
        if is_existential:
            body_lines.append(f"  -- NOTE: existential conclusion — `exact {last_step_name}` won't close the goal.")
            body_lines.append(f"  -- The existential witness + betweenness/construction proof needs manual fixup.")
            body_lines.append(f"  sorry")
        else:
            body_lines.append(f"  exact {last_step_name}")

    # Conclude sentence
    conclusion_idx = conclusion_entry["index"]
    loc = f"{book}.{prop}.{conclusion_idx}"
    body_lines.append(f'  euclid_conclude_sentence "{loc}"')
    body_lines.append(f'    "{text_for(conclusion_idx)}"')
    body_lines.append("")

    # Assemble the full file
    result_lines = header_lines + [""] + sig_lines + body_lines + [namespace_end, ""]

    return '\n'.join(result_lines)


def placeholder_entries(split_json: list) -> list:
    """Synthesize translate-style entries from split.json with `True` placeholder claims + `TODO`
    @assumptions — so --placeholders assembles a FILL-IN Main scaffold for /faithful-map. Text still
    comes from split.json (assemble_main uses split_text), so tiling is correct by construction.
    INDEX is the array POSITION (auto — the split agent never writes it)."""
    out = []
    for idx, e in enumerate(split_json):
        role = e["role"]
        if role in ("intro", "conclusion"):
            out.append({"index": idx, "role": role, "lean_claim": None})
            continue
        entry = {"index": idx, "role": role, "step_name": f"step{idx}", "lean_claim": "True",
                 "assumptions": [{"substring": j["substring"], "lean_type": "TODO"}
                                 for j in e.get("justifications", [])
                                 if isinstance(j, dict) and j.get("substring")]}
        if role == "construction":
            entry["construction"] = {"calls": []}      # /faithful-map adds the euclid_apply calls
        out.append(entry)
    return out


def main():
    parser = argparse.ArgumentParser(description="Assemble Main.lean (from translate.json, or from "
                                                 "split.json with --placeholders)")
    parser.add_argument("propdir", help="Proposition directory, e.g. Book2/Prop11")
    parser.add_argument("--placeholders", action="store_true",
                        help="assemble from split.json ALONE with `(stepN : True)` + `@assumption TODO` "
                             "placeholders (the fill-in scaffold for /faithful-map); no translate.json")
    parser.add_argument("--dry-run", action="store_true", help="Print output without writing")

    args = parser.parse_args()

    # Parse propdir
    parts = args.propdir.split("/")
    if len(parts) != 2:
        sys.exit(f"Expected Book<N>/PropNN, got: {args.propdir}")

    book_dir = parts[0]
    prop_name = parts[1]
    book_num = int(book_dir.replace("Book", ""))
    prop_num = int(prop_name.replace("Prop", ""))

    base = REPO_ROOT / book_dir / prop_name
    split_path = base / "split.json"
    translate_path = base / "translate.json"
    main_path = base / "Main.lean"

    if not split_path.exists():
        sys.exit(f"ERROR: {split_path} not found. Run /faithful-split first (and pass "
                 f"`check_faithful.py --split {args.propdir}`).")
    if not main_path.exists():
        sys.exit(f"ERROR: {main_path} not found.")

    split_json = json.loads(split_path.read_text())
    # TEXT source of truth: split.json, keyed by ARRAY POSITION (index is auto — not agent-written;
    # the --split gate guarantees it tiles in this order).
    split_text = {i: e["text"] for i, e in enumerate(split_json) if isinstance(e, dict)}

    if args.placeholders:
        # Fill-in scaffold for /faithful-map: True claims + TODO @assumptions, from split.json alone.
        translate_json = placeholder_entries(split_json)
    else:
        if not translate_path.exists():
            sys.exit(f"ERROR: {translate_path} not found. Run /faithful-translate first "
                     f"(or use --placeholders to stamp a fill-in scaffold for /faithful-map).")
        translate_json = json.loads(translate_path.read_text())
    result = assemble_main(translate_json, split_text, main_path, book_num, prop_num)

    if args.dry_run:
        print(result)
    else:
        main_path.write_text(result)
        print(f"Wrote: {main_path}")
        print(f"  {len(translate_json)} entries assembled")
        print(f"\nNext steps:")
        print(f"  python3 scripts/check_step.py {args.propdir} --provable")
        print(f"  python3 scripts/check_faithful.py \"{book_dir}/{prop_name}/Main.lean\"")


if __name__ == "__main__":
    main()
