#!/usr/bin/env python3
"""Faithfulness check (Design A) — pure text, no Lean, no SMT, instant.

Checks two of the three `Book2/faithful.txt` criteria (the third — statement-faithfulness — is
human-checked):

  CRITERION 1 (exact text recovery).  Concatenate the sentence texts in locator order and require
  the result to equal the canonical proposition source (Book 1: `Book/texts_proofs/{prop}.txt`;
  Book 2+: `Book{N}/data/texts_proofs/{prop}.txt`)
  CHARACTER-FOR-CHARACTER (only tolerance: a trailing newline at EOF). Three annotation forms
  participate, joined by a single space:
      euclid_sentence          — a logical proof step (emits a `have`)
      euclid_intro_sentence    — STRUCTURAL: enunciation + "I say that …" (attaches to euclid_intros)
      euclid_conclude_sentence — STRUCTURAL: closing restatement + QED (attaches to the final `exact`)

  CRITERION 3 (dependency reference, CONSTRUCTION-AWARE).  Every `[Prop.~B.N]` a sentence cites must be
  referenced by a `proposition_N` — as a CONSTRUCTION (`euclid_apply … as …` in Main, which may sit
  earlier than the citing sentence since objects are needed early) OR proof-internally (applied inside a
  step's helper). Satisfaction is WHOLE-MODULE, NOT block-scoped: source mode (number-only) checks the
  construction arm and DEFERS proof-internal cites to Phase B; olean mode (book-aware, transitive) checks
  both across the whole prop. This REFERENCES the dependency, it does not prove it is used — matching
  Euclid, who writes "by [Prop…]" without re-deriving.

TWO MODES:

  (default, source/regex — fast, offline, but NOT book-aware)
      python3 scripts/check_faithful.py "Book2/Prop01/Main.lean"
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
# Cone machinery (cone_names / propdir_of / prop_prefix) reused from the Phase-B lib so olean mode's
# notion of "the citing sentence's helper cone" is byte-identical to the number-only check.
import faithful_lib as fl

# ─────────────────────────────────────────────────────────────────────────────
# Shared helpers
# ─────────────────────────────────────────────────────────────────────────────

def norm(s: str) -> str:
    return " ".join(s.split())

# A citation in Euclid's text, e.g. [Prop.~1.11]  →  (book, num) = ("1", "11").
CITE = re.compile(r'\[Prop\.~(\d+)\.(\d+)\]')

# Bulk goal-closing tactics that must NOT appear in a faithful proof's MAIN body. A faithful proof
# closes its goal ONLY through the per-sentence `euclid_sentence` steps + their `euclid_apply`s (and
# `euclid_finish`/`euclid_intros`/`rw`/`exact`/`refine`/`constructor`). Any of these in the main file
# means the goal was likely cheat-closed by a leftover tactic from the old (unfaithful) proof, not by
# the faithful step chain. Only the proposition's MAIN file is linted; the per-sentence step files
# (`Book<N>/PropNN/stepN.lean`, theorem helper_<book>_stepN) are EXEMPT — scoped algebra is allowed in
# a step's own proof. Matched as whole words to avoid false hits inside identifiers.
FORBIDDEN_TACTICS = ["linarith", "nlinarith", "ring", "ring_nf", "simp", "omega",
                     "linear_combination", "norm_num", "field_simp", "polyrith"]
FORBIDDEN_RE = re.compile(r'(?<![\w.])(' + "|".join(FORBIDDEN_TACTICS) + r')(?![\w.])')

def is_helper_file(path: str) -> bool:
    """A file is a STEP/helper file (exempt from the forbidden-tactic lint) unless it is a proposition
    MAIN file. New layout: `Book<N>/PropNN/Main.lean` is linted; `Book<N>/PropNN/stepN.lean` (and any
    other non-Main file in a prop folder) is exempt. Legacy flat layouts (`PropNN.lean`,
    `*_steps.lean`, `Scratch/`) are still handled for safety."""
    p = path.replace("\\", "/")
    base = p.rsplit("/", 1)[-1]
    if "/Scratch/" in p or p.startswith("Scratch/") or p.endswith("_steps.lean"):
        return True
    # In a per-prop folder (.../PropNN/<file>.lean), only Main.lean is the linted proposition file.
    if re.search(r"/Prop\d+/", p):
        return base != "Main.lean"
    return False

def loc_key(loc: str):
    return [int(x) for x in loc.split(".") if x.isdigit()]

def canon_path_for(book: str, prop: str):
    """Resolve the canonical proof text relative to LeanEuclidPlus/.
    Book 1 is flat:       Book/texts_proofs/{prop}.txt
    Book 2+ is foldered:  Book{N}/data/texts_proofs/{prop}.txt  (data/ holds the generated corpus)."""
    if book == "1":
        rel = os.path.join("Book", "texts_proofs", f"{prop}.txt")
    else:
        rel = os.path.join(f"Book{book}", "data", "texts_proofs", f"{prop}.txt")
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
    if len(cw) == len(mw):
        # Same words in the same order, but the raw strings differ → a WHITESPACE mismatch: the source
        # has a multi-space run the single-space join didn't reproduce. Pinpoint it (still byte-exact to
        # PASS — this only makes the FAIL actionable so split/review can fix the boundary). See
        # faithful-split RULE 2: keep the extra space(s) inside a slice (trailing left / leading right).
        k = next((i for i in range(min(len(canon), len(concat))) if canon[i] != concat[i]),
                 min(len(canon), len(concat)))
        return False, ["whitespace mismatch — all words match, only spacing differs "
                       f"(first differs at char {k})",
                       f"  canonical: {canon[max(0, k-25):k+25]!r}",
                       f"  your text: {concat[max(0, k-25):k+25]!r}",
                       "  → the source has a multi-space run here; keep the extra space(s) INSIDE a "
                       "slice (trailing the left / leading the right) so the 1-space join reproduces it."]
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
    with spaces (newlines preserved) so byte offsets / line numbers are intact. String literals are
    passed through verbatim so a `--` INSIDE an annotation text (e.g. Euclid's "cut---equally") is
    not mistaken for a line comment."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        # A double-quoted string literal at top level (not inside a block comment) is copied as-is,
        # honoring Lean's `\"`/`\\` escapes, so embedded `--` / `/-` never reads as a comment.
        if depth == 0 and src[i] == '"':
            out.append(src[i]); i += 1
            while i < n:
                if src[i] == "\\" and i + 1 < n:
                    out.append(src[i]); out.append(src[i+1]); i += 2; continue
                out.append(src[i])
                if src[i] == '"':
                    i += 1; break
                i += 1
            continue
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

# any of the annotation tactics, then "loc" "text" — both strings allow escaped quotes \"
# (`wts` = mid-proof "I say that …" what-to-show: STRUCTURAL like intro/conclude — no claim binder,
#  but placement-unconstrained — so the True-gate skips it, the intro/conclude placement gate ignores
#  it, and only its text tiles.)
PAT = re.compile(
    r'euclid_(sentence|intro_sentence|conclude_sentence|wts)\s*'
    r'"((?:[^"\\]|\\.)*)"\s*"((?:[^"\\]|\\.)*)"')

def sentence_claim(src: str, start_pos: int):
    """Given `src` (comment-stripped) and a position at/after an `euclid_sentence`'s text string,
    return the claim type inside the following `(ident : CLAIM) :=`, whitespace-normalized, or None.
    Balances parens so nested `()` in the claim are handled. ONLY meaningful for `euclid_sentence`
    (intro/conclude sentences carry no `(name : claim)` binder)."""
    i = src.find("(", start_pos)
    if i < 0:
        return None
    depth, j = 0, i
    while j < len(src):
        if src[j] == "(":
            depth += 1
        elif src[j] == ")":
            depth -= 1
            if depth == 0:
                break
        j += 1
    else:
        return None
    m = re.match(r'\s*\w+\s*:\s*(.*)$', src[i + 1:j], re.DOTALL)   # "ident : CLAIM"
    return " ".join(m.group(1).split()) if m else None

_ASSUMPTION_TAGS = os.path.join(fl.BOOK_ROOT, "scripts", "assumption_tags.json")


def _assumption_tag_problems(main_path: str):
    """#2b (human Phase-C gate). Compare each assumption's CURRENT valid/gap (from its have body:
    inline `euclid_finish` → valid; else → gap) against the frozen scripts/assumption_tags.json the
    assumption phase wrote, AND confirm the structural pairing: a gap has a backing file (it must be
    proven), a valid is inline (no backing file). Empty ⟹ OK (also when no tags recorded yet)."""
    if not os.path.exists(_ASSUMPTION_TAGS):
        return []
    try:
        data = json.load(open(_ASSUMPTION_TAGS, encoding="utf-8"))
    except (ValueError, OSError):
        return []
    propdir = os.path.dirname(os.path.realpath(main_path))
    saved = data.get(os.path.relpath(propdir, fl.BOOK_ROOT))
    if not saved:
        return []
    current = fl.assumption_current_tags(main_path)
    problems = []
    for name, rec in sorted(saved.items()):
        want, have = rec.get("tag"), current.get(name)
        if have is None:
            problems.append(f"{name}: recorded '{want}' but its have is gone")
        elif have != want:
            problems.append(f"{name}: recorded '{want}' but is now '{have}'")
        else:
            bf = fl.backing_file(propdir, name)
            if want == "gap" and bf is None:
                problems.append(f"{name}: tagged 'gap' but has no backing file (a gap must be proven)")
            if want == "valid" and bf is not None:
                problems.append(f"{name}: tagged 'valid' (inline) but a backing file exists")
    return problems


def check_source(path: str) -> int:
    raw = open(path, encoding="utf-8").read()
    src = strip_comments(raw)
    anns = []
    for m in PAT.finditer(src):
        ln = src.count("\n", 0, m.start()) + 1
        anns.append({'loc': m.group(2), 'text': m.group(3).replace('\\"', '"').replace('\\\\', '\\'),
                     'kind': m.group(1), 'start': m.start(), 'end': m.end(),
                     'ref': f"{path}:{ln}"})
    print(f"=== {os.path.basename(path)} — MODE: source/regex (no build) ===")
    print("    quick offline sanity check (text is EXACT; dependency match is number-only, not book-aware)")
    if not anns:
        print("  [FAIL] no (uncommented) euclid_sentence annotations found")
        return 1

    # Structural check: contiguous locators, no duplicates.
    dg = report_dup_and_gap(anns, lambda it: it['ref'])
    if dg:
        return report("sentence locators are contiguous with no duplicates", False, ["see message above"])
    report("sentence locators are contiguous with no duplicates", True, [f"{len(anns)} sentences"])

    # TEXT MAP (faithful.txt criterion 1): all sentences present + concatenation reproduces the
    # original text exactly. Report this FIRST — it's the primary thing this mode verifies.
    book, prop, *_ = anns[0]['loc'].split(".")
    canon_rel, canon_path = canon_path_for(book, prop)
    ok1, lines1 = criterion1_exact(anns, canon_rel, canon_path)
    rc = report("all sentences present + concatenation reproduces the original text exactly",
                ok1, lines1)

    # DEPENDENCIES (faithful.txt criterion 3; CONSTRUCTION-AWARE, number-only, NOT book-aware):
    # a cited [Prop.~B.N] is satisfied iff `proposition_N` is applied WITH `as` ANYWHERE in Main — i.e.
    # it is a CONSTRUCTION (produces objects). `as` is the deterministic grammar marker (Solve.lean:
    # `euclid_apply term as ident(s)`). Presence-in-MAIN, NOT block-scoped — so a construction introduced
    # earlier than its citing sentence (objects are often needed early) is correctly accepted. A cited
    # prop that is NOT a Main construction is PROOF-INTERNAL: it lives inside a step's proof (helper cone),
    # which this single-file source check can't see — so it is DEFERRED to Phase B (`check_step
    # --dependency`, both arms) + gate C (olean, book-aware + transitive), NOT failed here. This is the
    # Phase-A construction-arm gate. The olean mode below is the authoritative book-aware check.
    constr_nums = {int(n) for n in re.findall(r'euclid_apply\s*\((.*?)\)\s*as\b', src, re.DOTALL)
                   for n in re.findall(r'proposition_(\d+)', n)}
    by_src = sorted(anns, key=lambda a: a['start'])
    deferred_counts, n_cites = {}, 0       # {(book,num): times cited proof-internally} — for a 1-line summary
    for a in by_src:
        for book, num in CITE.findall(a['text']):
            n_cites += 1
            if int(num) in constr_nums:
                continue                                   # construction arm — satisfied in Main
            deferred_counts[(book, num)] = deferred_counts.get((book, num), 0) + 1
    # Construction-arm failures would appear only if a cited construction prop had NO `… as …` in Main —
    # but we can't tell construction-intent from a number alone, so in SOURCE mode every non-Main-construction
    # citation is DEFERRED (informational), never a hard fail. Phase B / gate C enforce the proof arm.
    # Collapse the deferred list to ONE summary line (was one line per sentence — noisy on big props).
    def _fmt(bn, c):
        return f"{bn[0]}.{bn[1]}" + (f" (×{c})" if c > 1 else "")
    deferred_summary = ", ".join(_fmt(bn, c) for bn, c in sorted(deferred_counts.items(),
                                                                  key=lambda kv: (int(kv[0][0]), int(kv[0][1]))))
    lines = [f"{len(constr_nums)} construction prop(s) in Main: "
             f"{', '.join(f'proposition_{n}' for n in sorted(constr_nums)) or '(none)'}"]
    if deferred_counts:
        lines.append(f"{sum(deferred_counts.values())} proof-internal citation(s) deferred to Phase B "
                     f"(their step helpers must cite these): {deferred_summary}")
    rc |= report("every cited [Prop.~B.M] is a Main construction (`… as …`) or deferred to Phase B "
                 "(construction-aware, number-only)", True, lines)

    # NO CHEAT-CLOSED GOAL: a faithful MAIN proof must not close its goal with a bulk tactic left
    # over from the old proof. Lint the (comment-stripped) source for forbidden tactics. Helper/
    # scratch files are exempt. This is a heuristic guard, not a proof of faithfulness.
    if not is_helper_file(path):
        bad = []
        for m in FORBIDDEN_RE.finditer(src):
            ln = src.count("\n", 0, m.start()) + 1
            bad.append(f"`{m.group(1)}` at {path}:{ln} — bulk goal-closer not allowed in main "
                       f"(use the per-sentence euclid_sentence/euclid_apply chain; algebra goes in a helper)")
        rc |= report("no forbidden bulk goal-closing tactics in the main proof body",
                     not bad, bad or ["none found"])

    # @assumption text-substring check (criterion 4): every `-- @assumption ("text", ...)` annotation
    # must have its English text as a normalized substring of the owning euclid_sentence's text.
    # Scans the RAW source (annotations are comments, blanked in `src`). Positions align with `anns`
    # (strip_comments replaces comment chars with spaces — character offsets are identical in raw/src).
    assump_problems = []
    for am in fl.ASSUMPTION_ANNOT.finditer(raw):
        annot_text = am.group(1)
        # Find the next euclid_sentence after this annotation (by source position).
        after = [a for a in anns if a['start'] > am.start()]
        if not after:
            continue
        owner = min(after, key=lambda a: a['start'])
        if norm(annot_text) not in norm(owner['text']):
            snippet = owner['text'][:80] + ("..." if len(owner['text']) > 80 else "")
            assump_problems.append(
                f"@assumption text \"{annot_text}\" is not a substring of sentence {owner['loc']}: "
                f"\"{snippet}\"")
    if assump_problems:
        rc |= report("@assumption text is a normalized substring of its owning sentence",
                     False, assump_problems)
    elif fl.ASSUMPTION_ANNOT.search(raw):
        rc |= report("@assumption text is a normalized substring of its owning sentence",
                     True, [f"{sum(1 for _ in fl.ASSUMPTION_ANNOT.finditer(raw))} annotation(s) checked"])

    # NO VACUOUS `True` CLAIM (hard gate): every `euclid_sentence` must assert real content. A `True`
    # claim says Euclid's sentence is empty — almost never true and the classic all-`True` naive-map
    # failure. (`euclid_intro_sentence`/`euclid_conclude_sentence` carry no claim binder — skip them.)
    true_claims = []
    for a in anns:
        if a['kind'] != 'sentence':
            continue
        if sentence_claim(src, a['end']) == "True":
            true_claims.append(
                f"euclid_sentence {a['loc']} ({a['ref']}) has claim `True` — every sentence must "
                f"assert real content (a `True` claim says Euclid's sentence is empty); re-map it.")
    rc |= report("no euclid_sentence has a vacuous `True` claim",
                 not true_claims, true_claims or [f"{sum(1 for a in anns if a['kind'] == 'sentence')} "
                                                  "sentence claim(s) are non-trivial"])

    # STRUCTURAL PLACEMENT (hard gate): `euclid_intro_sentence`/`euclid_conclude_sentence` are STRUCTURAL —
    # they carry no claim and must bracket the proof (intro before the first euclid_sentence, conclude
    # after the last). A mid-body intro/conclude is a faithfulness DODGE (see fl.intro_conclude_placement).
    place_problems = fl.intro_conclude_placement_problems(anns)
    rc |= report("euclid_intro/conclude_sentence bracket the proof (leading / trailing only)",
                 not place_problems, place_problems or ["placement OK"])

    # ASSUMPTION TAG GATE (#2b, human Phase-C): each assumption's valid/gap (from its have body) must
    # match scripts/assumption_tags.json (written by the assumption phase); a gap must be backed, a valid
    # stays inline. No-op until the prop has been run through the phase.
    tag_problems = _assumption_tag_problems(path)
    rc |= report("assumption valid/gap tags unchanged (+ gaps backed, valids inline)",
                 not tag_problems, tag_problems or ["tags match assumption_tags.json (or none recorded)"])

    # Reminder: the third faithfulness criterion (each step's TYPE honestly captures its sentence)
    # is HUMAN-checked — no machine verifies it.
    print("  [note] not machine-checked: that each step's type honestly captures its sentence (review by hand)")

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
    print(f"=== {os.path.basename(json_path)} — MODE: --olean (compiled, AUTHORITATIVE) ===")
    print("    text reproduction is EXACT; dependency match is BOOK-AWARE + transitive (resolved names)")
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
        rc |= report("sentence locators are contiguous with no duplicates", not dg,
                     ["see message above"] if dg else [f"{len(sents)} sentences"])

        # CRITERION 3 (book-aware, TWO-ARM — construction vs. proof). A cited [Prop.~B.N] is satisfied
        # iff some applied constant matches Book B's prop N (by RESOLVED identity — `name_matches`, the
        # book-aware gate) in EITHER arm:
        #   • construction arm — applied `… as …` ANYWHERE in this prop's `…Main` module. Whole-Main, NOT
        #     block-scoped: figure objects are routinely hoisted EARLIER than the citing sentence (the
        #     vetted Prop03 `proposition_31 as AF` case). Every Main proposition-apply is an `as`
        #     construction (verified invariant), so "applied in the Main module" IS the construction arm.
        #   • proof arm — applied (no `as`) INSIDE the citing sentence's helper CONE (its stepN backing
        #     file + transitive sub-files). Scoped STRICTLY to that cone: the post-relocation layout puts
        #     each step in its own module, so a proof-internal cite lives outside Main.
        # The cone is the `have`-containment cone (`fl.cone_names`), identical to the Phase-B number-only
        # `dependency_problems` — so the two gates can't disagree on structure; only the name-match
        # granularity differs (book-aware here, number-only there). The export's per-`euclid_apply`
        # `appliedExt` record (the `applied` array, keyed by module) is the reliable source: the `deps`
        # transitive closure is empty for SMT-discharged applies (the prop never lands in the term), so
        # it is NOT used. Criterion 3 is a REFERENCE check (Euclid writes "by [Prop X]").
        main_mod = sents[0]['mod']
        propdir = None
        if main_mod.endswith(".Main"):
            try:                                                      # Book2.Prop05.Main -> Book2/Prop05
                propdir = fl.propdir_of(main_mod[:-len(".Main")].replace(".", os.sep))
            except fl.FaithfulError:
                propdir = None                                        # no folder on disk → construction arm only
        mod_prefix = fl.prop_prefix(propdir) if propdir else None     # e.g. "Book2.Prop05"
        # locator → node name (authoritative map from the parsed `have`/sentence tree, not a name guess).
        try:
            occ = fl.parse_occurrences(propdir) if propdir else {}
        except fl.FaithfulError:
            occ = {}
        node_by_loc = {nd.loc: nm for nm, nds in occ.items() for nd in nds
                       if nd.kind == "sentence" and nd.loc is not None}
        construction = applied_by_mod.get(main_mod, [])               # whole-Main `as` constructions
        dep_lines, n_cites = [], 0
        for s in sents:
            if s.get('kind') == 'structural':
                continue                                              # intro/conclude/wts: background citations, not proof steps
            for cbook, num in CITE.findall(s['text']):
                n_cites += 1
                if any(name_matches(ap['name'], cbook, num) for ap in construction):
                    continue                                          # construction arm
                # proof arm: search the citing sentence's cone modules (if it has a node + we found the dir).
                cone_hit = False
                node = node_by_loc.get(s['loc'])
                if node is not None and propdir is not None:
                    try:
                        cone = fl.cone_names(propdir, node)
                    except fl.FaithfulError:
                        cone = set()
                    cone_mods = {f"{mod_prefix}.{n}" for n in cone}
                    cone_hit = any(name_matches(ap['name'], cbook, num)
                                   for m in cone_mods for ap in applied_by_mod.get(m, []))
                if cone_hit:
                    continue
                where = f"its helper cone (node `{node}`)" if node else \
                        "any helper cone (structural sentence — must be a Main construction)"
                dep_lines.append(f"{s['loc']} ({s['ref']}) cites [Prop.~{cbook}.{num}] but no "
                                 f"`proposition_{num}` of Book {cbook} is applied `… as …` in {main_mod} "
                                 f"(construction) nor inside {where}")
        rc |= report("every cited [Prop.~B.M] is referenced in the prop (book-aware: Main construction or sentence's cone)",
                     not dep_lines,
                     dep_lines or [f"all {n_cites} citation(s) resolve to the cited book+number"])

        canon_rel, canon_path = canon_path_for(book, prop)
        ok1, lines1 = criterion1_exact(sents, canon_rel, canon_path)
        rc |= report("all sentences present + concatenation reproduces the original text exactly",
                     ok1, lines1)

    # Reminder: that each step's TYPE honestly captures its sentence is HUMAN-checked — not here.
    print("  [note] not machine-checked: that each step's type honestly captures its sentence (review by hand)")
    print(f"  => {'ALL PASS' if rc == 0 else 'FAILED'} (--olean mode, authoritative)")
    return rc

# ─────────────────────────────────────────────────────────────────────────────

def check_split(propdir: str) -> int:
    """--split mode (Phase-A stage-1 gate): verify Book<N>/PropNN/split.json TILES the canonical text
    byte-for-byte BEFORE translate/assemble is paid for. Reuses criterion1_exact, so a whitespace-only
    miss gets the same actionable "char N" diagnostic. Reads split.json + the canonical .txt; and, on
    deduction entries carrying the OPT-IN "spans" field, checks the assertion/assumption/glue spans
    reconstruct the sentence char-for-char (and warns on a compound assertion span).
    Run this right after faithful-split and fix the slices until it PASSES."""
    base = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))       # LeanEuclidPlus/
    pd = propdir if os.path.isabs(propdir) else os.path.join(base, propdir)
    sp = os.path.join(pd, "split.json")
    print(f"=== --split — {propdir.rstrip('/')}/split.json vs canonical ===")
    m = re.search(r'Book(\d+)[/\\]+Prop0*(\d+)', propdir)
    if not m:
        print(f"  [FAIL] cannot parse Book<N>/Prop<NN> from: {propdir}")
        return 1
    book, prop = m.group(1), m.group(2)
    if not os.path.exists(sp):
        print(f"  [FAIL] split.json not found: {os.path.relpath(sp, base)}")
        return 1
    try:
        data = json.load(open(sp, encoding="utf-8"))
    except ValueError as e:
        print(f"  [FAIL] split.json is not valid JSON: {e}")
        return 1
    if not isinstance(data, list) or not data:
        print("  [FAIL] split.json must be a non-empty JSON array")
        return 1
    # INDEX = array position (auto — the split agent never writes it); the array is already in order.
    items = [{'loc': f"{book}.{prop}.{i}", 'text': e.get('text', ''),
              'ref': f"split.json[{i}]"} for i, e in enumerate(data)]
    canon_rel, canon_path = canon_path_for(book, prop)
    ok, lines = criterion1_exact(items, canon_rel, canon_path)
    rc = report("split.json tiles the canonical text byte-for-byte (whitespace included)", ok, lines)

    # OPT-IN assertion/assumption discipline: only entries carrying a "spans" field are checked, so
    # legacy split.json (no spans) is completely unaffected. Each span is {"label": assertion|assumption|
    # glue, "text": <verbatim slice>}. (a) HARD: the spans must reconstruct the sentence CHARACTER-FOR-
    # CHARACTER (empty join — no separator — every weird/double/trailing space included). (b) WARN: an
    # `assertion` span with a comma or " and " is likely a compound claim to split (the AI decides).
    concat_fails, warn_lines = [], []
    for i, e in enumerate(data):
        if not isinstance(e, dict) or not e.get("spans"):
            continue
        spans, ref, txt = e["spans"], f"split.json[{i}]", e.get("text", "")
        joined = "".join(sp.get("text", "") for sp in spans if isinstance(sp, dict))
        if joined != txt:
            k = next((c for c in range(min(len(joined), len(txt))) if joined[c] != txt[c]),
                     min(len(joined), len(txt)))
            concat_fails += [f"{ref}: spans do not reconstruct the sentence (first differ at char {k})",
                             f"    text : {txt[max(0, k - 20):k + 20]!r}",
                             f"    spans: {joined[max(0, k - 20):k + 20]!r}"]
        for sp in spans:
            if isinstance(sp, dict) and sp.get("label") == "assertion":
                a = sp.get("text", "")
                if "," in a or " and " in norm(a):
                    warn_lines.append(f"{ref} assertion span may be COMPOUND (has ',' or ' and '): {norm(a)!r}")
    rc |= report("deduction spans reconstruct their sentence char-for-char (opt-in)",
                 not concat_fails,
                 concat_fails or ["no `spans` fields present, or all reconstruct exactly"])
    for w in warn_lines:
        print(f"  [warn] {w}")
        print( "         → likely two claims; split into atomic entries (AI makes the final call)")

    # REDUCTIO FRAMES (opt-in): entries carrying a `frame` object drive the assembler's nested
    # `have habsurd … := by intro …` skeleton. They must form well-formed triples, LINKED BY TEXT (no
    # indices): a `reductio_close`'s `closes` copies its `reductio_open`'s `supposition` VERBATIM, with a
    # `contradiction` sitting between them. This catches a malformed reductio at split time — before the
    # assembler stamps a broken block. (`wts` role + a frame-free split are completely unaffected.)
    frames = [(i, e["frame"]) for i, e in enumerate(data)
              if isinstance(e, dict) and isinstance(e.get("frame"), dict) and e["frame"].get("kind")]
    frame_problems = []
    if frames:
        KNOWN = {"reductio_open", "contradiction", "reductio_close"}
        opens  = [(i, fr.get("supposition")) for i, fr in frames if fr["kind"] == "reductio_open"]
        closes = [(i, fr.get("closes"))      for i, fr in frames if fr["kind"] == "reductio_close"]
        contras = [i for i, fr in frames if fr["kind"] == "contradiction"]
        for i, fr in frames:
            if fr["kind"] not in KNOWN:
                frame_problems.append(f"split.json[{i}]: unknown frame kind {fr['kind']!r} (expected "
                                      "reductio_open / contradiction / reductio_close)")
        for i, supp in opens:
            if not supp:
                frame_problems.append(f"split.json[{i}]: reductio_open has no `supposition` text")
                continue
            match = [j for j, c in closes if c and norm(c) == norm(supp)]
            if not match:
                frame_problems.append(f"split.json[{i}]: reductio_open supposition {norm(supp)!r} has no "
                                      "matching reductio_close (a close's `closes` must copy it verbatim)")
                continue
            j = match[0]
            if j < i:
                frame_problems.append(f"split.json[{i}]: its reductio_close at [{j}] precedes the open")
            elif not any(i < k < j for k in contras):
                frame_problems.append(f"split.json[{i}]: no `contradiction` frame between the open and its "
                                      f"close at [{j}]")
        for j, c in closes:
            if not c:
                frame_problems.append(f"split.json[{j}]: reductio_close has no `closes` text")
            elif not any(s and norm(s) == norm(c) for _, s in opens):
                frame_problems.append(f"split.json[{j}]: reductio_close `closes` {norm(c)!r} matches no "
                                      "reductio_open `supposition`")
        if contras and not opens:
            frame_problems.append("a `contradiction` frame is present but no `reductio_open` opens it")
        rc |= report("reductio frames form well-formed open/contradiction/close triples (linked by text)",
                     not frame_problems, frame_problems or [f"{len(opens)} reductio(s) well-formed"])

    print(f"  => {'PASS' if rc == 0 else 'FAILED'} (--split mode)")
    return rc

def main(argv) -> int:
    if len(argv) == 2 and argv[0] == "--olean":
        return check_olean(argv[1])
    if len(argv) == 2 and argv[0] == "--split":
        return check_split(argv[1])
    if len(argv) == 1 and not argv[0].startswith("--"):
        return check_source(argv[0])
    print(__doc__)
    return 2

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
