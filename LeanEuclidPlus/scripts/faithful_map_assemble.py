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
                        # Book 1 props live in the FOLDERED Book1/ tree (Book1/PropNN/Main.lean,
                        # module Book1.PropNN.Main, namespace Elements.Book1). The flat Book/ tree is
                        # DEAD — never import it. Construction props are almost always Book 1.
                        imports.append(f"import Book1.Prop{prop_num:02d}.Main")

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
        # Escape for Lean string-literal emission: a lone backslash (LaTeX artifacts like \dag / \kern
        # in the Fitzpatrick text) is an invalid Lean escape, and a raw " would close the string. The
        # source-mode check_faithful decodes these back before comparing to the canonical text, and the
        # olean mode sees the compiler-decoded string — so the canonical .txt stays pristine.
        return split_text[idx].replace("\\", "\\\\").replace('"', '\\"')

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

    # Emit each step. `indent` tracks reductio nesting: a `reductio_open` frame stamps a
    # `have habsurd<k> : ¬(sorry) := by / intro hsuppose<k>` block and deepens the indent by one; the
    # matching `contradiction` frame stamps `exact <False-step>` and pops back out, so the trailing
    # `reductio_close` (and everything after) lands at the outer level automatically. The script stamps
    # ONLY the reductio frame — text-signalled by "For if…" / "impossible" / "Thus … not …" — NOT
    # split_ors/by_cases/wlog, which the map agent adds. At depth 1 the output is byte-identical to a
    # frame-free prop (sp()="  ", sp(1)="    ").
    indent = 1

    def sp(extra=0):
        return "  " * (indent + extra)

    def emit_step(entry):
        """Emit construction calls + @assumption annotations + the euclid_sentence for one step at the
        CURRENT indent. Returns the step name."""
        step_name = entry["step_name"]
        step_idx = int(step_name.replace("step", ""))
        loc = f"{book}.{prop}.{step_idx}"
        if entry.get("construction") and entry["construction"].get("calls"):
            for line in format_construction_calls(entry["construction"]):
                body_lines.append(sp() + line.lstrip())
        for assumption in entry.get("assumptions", []):
            body_lines.append(sp() + format_assumption_annotation(assumption).lstrip())
        claim = entry["lean_claim"]
        body_lines.append(f'{sp()}euclid_sentence "{loc}"')
        body_lines.append(f'{sp(1)}"{text_for(entry.get("index", step_idx))}"')
        body_lines.append(f'{sp(1)}({step_name} : {claim}) := by sorry')
        body_lines.append("")
        return step_name

    last_step_name = None          # last TOP-LEVEL step — the final `exact` target (inside-block steps skip)
    habsurd_count = 0
    for entry in step_entries:
        role = entry.get("role")
        frame = entry.get("frame") or {}
        kind = frame.get("kind")

        # wts — mid-proof "I say that …" what-to-show: STRUCTURAL, no claim binder → euclid_wts.
        if role == "wts":
            idx = entry.get("index")
            loc = f"{book}.{prop}.{idx}"
            body_lines.append(f'{sp()}euclid_wts "{loc}"')
            body_lines.append(f'{sp(1)}"{text_for(idx)}"')
            body_lines.append("")
            continue

        if kind == "reductio_open":
            habsurd_count += 1
            # ¬(sorry) = the negation of the supposition; the map agent fills the ≠ expression and makes
            # the trailing reductio_close claim match. `intro` names the supposition hypothesis.
            body_lines.append(f'{sp()}have habsurd{habsurd_count} : ¬(sorry) := by')
            indent += 1
            body_lines.append(f'{sp()}intro hsuppose{habsurd_count}')
            emit_step(entry)       # the open sentence's own claim (e.g. the ∨) lives inside the block
            continue

        if kind == "contradiction":
            sname = emit_step(entry)   # claim pre-set to `False`
            if body_lines and body_lines[-1] == "":
                body_lines.pop()       # keep `exact` flush against the impossible-sentence, then blank
            body_lines.append(f'{sp()}exact {sname}')
            body_lines.append("")
            indent = max(1, indent - 1)
            continue

        sname = emit_step(entry)       # normal step (a reductio_close is just an outer-level step)
        if indent == 1:
            last_step_name = sname

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
        # wts — mid-proof "I say that …": STRUCTURAL, no claim (assembles to euclid_wts, no stepN).
        if role == "wts":
            out.append({"index": idx, "role": "wts"})
            continue
        # @assumption seeds: prefer the opt-in `spans` (assumption-label slices); else fall back to the
        # legacy `justifications` (byte-identical output for split.json without spans).
        spans = e.get("spans")
        if spans:
            assumptions = [{"substring": sp["text"], "lean_type": "TODO"}
                           for sp in spans
                           if isinstance(sp, dict) and sp.get("label") == "assumption" and sp.get("text")]
        else:
            assumptions = [{"substring": j["substring"], "lean_type": "TODO"}
                           for j in e.get("justifications", [])
                           if isinstance(j, dict) and j.get("substring")]
        # reductio frame (opt-in): reductio_open/contradiction/reductio_close drive the assembler's
        # nested `have habsurd … := by intro …` skeleton. A contradiction sentence's claim is `False`
        # (it reaches the absurdity, not a new geometric fact); everything else starts `True`.
        frame = e.get("frame") if isinstance(e.get("frame"), dict) else None
        kind = frame.get("kind") if frame else None
        claim = "False" if kind == "contradiction" else "True"
        entry = {"index": idx, "role": role, "step_name": f"step{idx}", "lean_claim": claim,
                 "assumptions": assumptions}
        if role == "construction":
            entry["construction"] = {"calls": []}      # /faithful-map adds the euclid_apply calls
        if frame and kind:
            entry["frame"] = frame
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
