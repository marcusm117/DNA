#!/usr/bin/env python3
"""Faithfulness check (Design A) — pure text, no Lean, no SMT, instant.

Checks two of the three `Book2/faithful.txt` criteria (the third — statement-faithfulness — is
human-checked):

  CRITERION 1 (exact text recovery).  Concatenate the sentence texts in locator order and require
  the result to equal the canonical proposition source `Book{N}/texts_proofs/{prop}.txt`
  CHARACTER-FOR-CHARACTER (only tolerance: a trailing newline at EOF). Three annotation forms
  participate, joined by a single space:
      euclid_sentence          — a logical proof step (emits a `have`)
      euclid_intro_sentence    — STRUCTURAL: enunciation + "I say that …" (attaches to euclid_intros)
      euclid_conclude_sentence — STRUCTURAL: closing restatement + QED (attaches to the final `exact`)

  CRITERION 3 (dependency reference).  For each sentence, every `[Prop.~B.N]` Euclid cites must be
  referenced by a `proposition_N` in that sentence's BLOCK (scope A: the source between the previous
  sentence and this one). This REFERENCES the dependency, it does not prove it is used — matching
  Euclid, who writes "by [Prop…]" without re-deriving.

TWO MODES:

  (default, source/regex — fast, offline, but NOT book-aware)
      python3 scripts/check_faithful.py "Book2/Prop01.lean"
  Reads the annotations + `euclid_apply` lines straight from the .lean source. The criterion-3 check
  only matches the proposition NUMBER (`[Prop.~1.34]` is satisfied by any `proposition_34`); it does
  not authenticate the book B. Use for quick edits before a build.

  (--olean — CERTAIN, book-aware)
      lake exe faithful_export Book2 > out.json
      python3 scripts/check_faithful.py --olean out.json
  Reads the JSON dumped from the compiled `.olean` by `faithful_export`. Texts are what the compiler
  elaborated; each cited `[Prop.~B.N]` is matched against the COMPILER-RESOLVED fully-qualified
  constant (e.g. `Elements.Book1.proposition_34'`), so the book is authenticated. Covers every
  proposition in the loaded module at once. This supersedes the source/regex stopgap.

Neither mode verifies that the proof compiles — that is the *correctness* axis (`lake build`).
"""
import re, sys, os, json

# ─────────────────────────────────────────────────────────────────────────────
# Shared helpers
# ─────────────────────────────────────────────────────────────────────────────

def norm(s: str) -> str:
    return " ".join(s.split())

# A citation in Euclid's text, e.g. [Prop.~1.11]  →  (book, num) = ("1", "11").
CITE = re.compile(r'\[Prop\.~(\d+)\.(\d+)\]')

def loc_key(loc: str):
    return [int(x) for x in loc.split(".") if x.isdigit()]

def canon_path_for(book: str, prop: str):
    """Resolve Book{N}/texts_proofs/{prop}.txt relative to LeanEuclidPlus/."""
    rel = os.path.join("Book" if book == "1" else f"Book{book}", "texts_proofs", f"{prop}.txt")
    base = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # LeanEuclidPlus/
    return rel, os.path.join(base, rel)

def name_matches(name: str, book: str, num: str) -> bool:
    """True if the resolved fully-qualified constant `name` (e.g. 'Elements.Book1.proposition_34'')
    is proposition `num` of book `book` — BOOK-AWARE. Primes after the number are allowed; a trailing
    digit is not (so proposition_3 ≠ proposition_34)."""
    return (re.search(rf'Book{book}\b', name) is not None
            and re.search(rf'proposition_{num}(?!\d)', name) is not None)

def report_dup_and_gap(items, ref_of) -> int:
    """items: list of dicts with 'loc'. ref_of(item) -> 'file:line' for messages. Returns 1 on
    duplicate or gap in the last locator segment, else 0."""
    locs = [it['loc'] for it in items]
    dups = sorted({l for l in locs if locs.count(l) > 1})
    if dups:
        for loc in dups:
            refs = [ref_of(it) for it in items if it['loc'] == loc]
            print(f"FAIL: duplicate locator {loc} at {','.join(refs)}")
        return 1
    keys = sorted(loc_key(l) for l in locs)
    last = [k[-1] for k in keys]
    if last and last == sorted(last):
        missing = [n for n in range(last[0], last[-1] + 1) if n not in last]
        if missing:
            stem = ".".join(map(str, keys[0][:-1]))
            print(f"FAIL: gap in locators — missing {', '.join(f'{stem}.{m}' for m in missing)}")
            return 1
    return 0

def criterion1_exact(items, canon_rel, canon_path):
    """items: list of dicts with 'loc','text','ref' (the right set for ONE prop), in any order.
    Concatenate in locator order, compare char-for-char to the canonical text.
    Returns (ok: bool, lines: list[str]) — caller prints. Does not print."""
    if not os.path.exists(canon_path):
        return False, [f"canonical source not found: {canon_rel}"]
    canon = open(canon_path, encoding="utf-8").read().rstrip("\n")

    ordered = sorted(items, key=lambda it: loc_key(it['loc']))
    concat = " ".join(it['text'] for it in ordered)
    span = f"{len(ordered)} sentences ({ordered[0]['loc']}..{ordered[-1]['loc']}) vs {canon_rel}"

    if concat == canon:
        return True, [f"concatenation reproduces canonical text exactly, in order ({span})"]

    cw, mw = canon.split(), concat.split()
    for j in range(min(len(cw), len(mw))):
        if cw[j] != mw[j]:
            loc = ordered_loc_at(ordered, j)
            ref = next((it['ref'] for it in ordered if it['loc'] == loc), ordered[-1]['ref'])
            ctx = " ".join(mw[max(0, j-4):j])
            return False, [f"diverges at {loc} ({ref})",
                           f"  ...{ctx} <HERE>",
                           f"  canonical: {cw[j]!r}",
                           f"  your text: {mw[j]!r}"]
    if len(mw) < len(cw):
        return False, [f"canonical text continues past your last sentence — "
                       f"missing (e.g.) {' '.join(cw[len(mw):len(mw)+8])!r} ..."]
    return False, [f"your text runs past the end of the canonical text: "
                   f"{' '.join(mw[len(cw):len(cw)+8])!r} ..."]

def report(criterion: str, ok: bool, lines):
    """Print a uniform per-criterion result block. Returns 0 if ok else 1."""
    tag = "[PASS]" if ok else "[FAIL]"
    print(f"  {tag} {criterion}")
    for ln in lines:
        print(f"         {ln}")
    return 0 if ok else 1

def ordered_loc_at(ordered, word_index):
    """Which sentence locator owns word number `word_index` in the concatenation."""
    i = 0
    for it in ordered:
        n = len(it['text'].split())
        if word_index < i + n:
            return it['loc']
        i += n
    return ordered[-1]['loc']

# ─────────────────────────────────────────────────────────────────────────────
# MODE 1 — source/regex (fast, offline, NOT book-aware)
# ─────────────────────────────────────────────────────────────────────────────

def strip_comments(src: str) -> str:
    """Blank out Lean `--` line and nested `/- … -/` block comments, REPLACING comment characters
    with spaces (newlines preserved) so byte offsets / line numbers are intact."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        two = src[i:i+2]
        if depth == 0 and two == "--":
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
            continue
        if two == "/-":
            depth += 1; out.append("  "); i += 2; continue
        if two == "-/" and depth > 0:
            depth -= 1; out.append("  "); i += 2; continue
        if depth > 0:
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        out.append(src[i]); i += 1
    return "".join(out)

# any of the three annotation tactics, then "loc" "text" — both strings allow escaped quotes \"
PAT = re.compile(
    r'euclid_(sentence|intro_sentence|conclude_sentence)\s*'
    r'"((?:[^"\\]|\\.)*)"\s*"((?:[^"\\]|\\.)*)"')

def check_source(path: str) -> int:
    raw = open(path, encoding="utf-8").read()
    src = strip_comments(raw)
    anns = []
    for m in PAT.finditer(src):
        ln = src.count("\n", 0, m.start()) + 1
        anns.append({'loc': m.group(2), 'text': m.group(3).replace('\\"', '"'),
                     'start': m.start(), 'ref': f"{path}:{ln}"})
    print(f"=== {os.path.basename(path)} — MODE: source/regex (no build) ===")
    print("    criterion 1 (text map): EXACT   |   criterion 3 (deps): NUMBER-ONLY, not book-aware")
    if not anns:
        print("  [FAIL] no (uncommented) euclid_sentence annotations found")
        return 1

    # Structural check: contiguous locators, no duplicates.
    dg = report_dup_and_gap(anns, lambda it: it['ref'])
    if dg:
        return report("locators (contiguous, no dups)", False, ["see message above"])
    report("locators (contiguous, no dups)", True, [f"{len(anns)} sentences"])

    # CRITERION 3 (regex stopgap, NOT book-aware): each cited [Prop.~B.N] referenced by a
    # `proposition_N` in the sentence's block (between the previous annotation and this one).
    by_src = sorted(anns, key=lambda a: a['start'])
    dep_lines, n_cites = [], 0
    for idx, a in enumerate(by_src):
        cites = CITE.findall(a['text'])
        block = src[(by_src[idx - 1]['start'] if idx > 0 else 0):a['start']]
        for book, num in cites:
            n_cites += 1
            if not re.search(rf'proposition_{num}(?!\d)', block):
                dep_lines.append(f"{a['loc']} ({a['ref']}) cites [Prop.~{book}.{num}] but no "
                                 f"`proposition_{num}` in its block")
    rc = report("criterion 3 — dependencies (number-only)",
                not dep_lines,
                dep_lines or [f"all {n_cites} citation(s) referenced in their block"])

    # CRITERION 1.
    book, prop, *_ = anns[0]['loc'].split(".")
    canon_rel, canon_path = canon_path_for(book, prop)
    ok1, lines1 = criterion1_exact(anns, canon_rel, canon_path)
    rc |= report("criterion 1 — exact text map", ok1, lines1)

    # Soft warning: identical sentence texts (intro enunciation ≈ conclusion restatement is expected).
    seen = {}
    for a in sorted(anns, key=lambda x: loc_key(x['loc'])):
        nt = norm(a['text'])
        if nt in seen:
            print(f"  [warn] {a['loc']} ({a['ref']}) has identical text to {seen[nt]}")
        else:
            seen[nt] = a['loc']

    print(f"  => {'ALL PASS' if rc == 0 else 'FAILED'} (source/regex mode)")
    return rc

# ─────────────────────────────────────────────────────────────────────────────
# MODE 2 — --olean (certain, book-aware) over faithful_export JSON
# ─────────────────────────────────────────────────────────────────────────────

def check_olean(json_path: str) -> int:
    data = json.load(open(json_path, encoding="utf-8"))
    sentences = data.get("sentences", [])
    applied   = data.get("applied", [])
    print(f"=== {os.path.basename(json_path)} — MODE: --olean (compiled, CERTAIN) ===")
    print("    criterion 1 (text map): EXACT   |   criterion 3 (deps): BOOK-AWARE (resolved names)")
    if not sentences:
        print("  [FAIL] no sentences in JSON (did you build the module before faithful_export?)")
        return 1

    applied_by_mod = {}
    for ap in applied:
        applied_by_mod.setdefault(ap['mod'], []).append(ap)

    # group sentences by proposition (book, prop) = first two locator segments.
    groups = {}
    for s in sentences:
        parts = s['loc'].split(".")
        groups.setdefault((parts[0], parts[1]), []).append(s)

    rc = 0
    for (book, prop), sents in sorted(groups.items(),
                                      key=lambda kv: loc_key(f"{kv[0][0]}.{kv[0][1]}")):
        print(f"--- Book{book} Prop {prop} ---")
        for s in sents:
            s['ref'] = f"{s['mod']}:{s['line']}"

        dg = report_dup_and_gap(sents, lambda it: it['ref'])
        rc |= report("locators (contiguous, no dups)", not dg,
                     ["see message above"] if dg else [f"{len(sents)} sentences"])

        # CRITERION 3 (book-aware, scope A): block = applies in the SAME module with line strictly
        # after the previous sentence and up to this sentence (ordered by line).
        ordered_by_line = sorted(sents, key=lambda x: x['line'])
        dep_lines, n_cites = [], 0
        for i, s in enumerate(ordered_by_line):
            cites = CITE.findall(s['text'])
            prev_line = ordered_by_line[i - 1]['line'] if i > 0 else -1
            block = [ap for ap in applied_by_mod.get(s['mod'], [])
                     if prev_line < ap['line'] <= s['line']]
            for cbook, num in cites:
                n_cites += 1
                if not any(name_matches(ap['name'], cbook, num) for ap in block):
                    names = ", ".join(sorted({ap['name'] for ap in block})) or "(none)"
                    dep_lines.append(f"{s['loc']} ({s['ref']}) cites [Prop.~{cbook}.{num}] but no "
                                     f"matching applied prop in block; block applies: {names}")
        rc |= report("criterion 3 — dependencies (book-aware)",
                     not dep_lines,
                     dep_lines or [f"all {n_cites} citation(s) resolve to the cited book+number"])

        canon_rel, canon_path = canon_path_for(book, prop)
        ok1, lines1 = criterion1_exact(sents, canon_rel, canon_path)
        rc |= report("criterion 1 — exact text map", ok1, lines1)

    print(f"  => {'ALL PASS' if rc == 0 else 'FAILED'} (--olean mode, criteria 1 + 3)")
    return rc

# ─────────────────────────────────────────────────────────────────────────────

def main(argv) -> int:
    if len(argv) == 2 and argv[0] == "--olean":
        return check_olean(argv[1])
    if len(argv) == 1 and not argv[0].startswith("--"):
        return check_source(argv[0])
    print(__doc__)
    return 2

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
