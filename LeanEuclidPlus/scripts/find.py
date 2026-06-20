#!/usr/bin/env python3
"""`find.py` — the sanctioned smart-grep over the System-E fact database (`.lake/index.jsonl`).

This is the QUERY half of "idea 01" (docs/ideas/01-conclusion-index.md). The DB (baked by
`bake_index.py`) is dumb and complete; the intelligence is here, in the FILTERS. Instead of reading
`SystemE/Theory/Inferences/*.lean` and guessing signatures, ask the DB directly along any axis. It
re-bakes incrementally on every run (only changed .lean files re-parse), so results are always fresh.

USAGE (run BARE from LeanEuclidPlus/, never piped):
    python3 scripts/find.py --concludes "¬intersectsLine"   # what gets me 'parallel' (backward)
    python3 scripts/find.py --consumes formParallelogram     # I HAVE a parallelogram — what uses it (forward)
    python3 scripts/find.py --mentions intersectsLine --kind axiom   # the opaque def's behavior = its axioms
    python3 scripts/find.py --name "proposition_29*"         # the whole primed family, side-by-side
    python3 scripts/find.py --book 2 --name proposition_1    # Book 2's prop 1 (Book 1 also has one)
    python3 scripts/find.py --cites proposition_30           # worked examples that USE Prop 30
    python3 scripts/find.py --depends-of helper_2_1_step5    # what a decl cites (its foundation)
    python3 scripts/find.py --grep "repackaged"              # full-text over docstrings (search by intent)
    python3 scripts/find.py --book 2 --prop 5 --kind step    # Prop05's step backing-files

FILTERS (combinable — AND-ed together):
    --concludes SYM   row has a fact with role=concl and this symbol      (leading ¬ ⟹ polarity=neg)
    --consumes  SYM   row has a fact with role=hyp  and this symbol       (leading ¬ ⟹ polarity=neg)
    --mentions  SYM   row has this symbol in ANY role                     (leading ¬ ⟹ polarity=neg)
       ↑ these three are REPEATABLE and comma-splittable, AND-ed: `--consumes formParallelogram,onLine`
         (or `--consumes formParallelogram --consumes onLine`) = rows that consume BOTH.
    --kind      K     restrict kind ∈ {axiom,def,abbrev,opaque,prop,helper,step,theorem}  (comma-list ok)
    --book      N     restrict to a book: 1 ⟹ Book/ , 2 ⟹ Book2/ , …  (SystemE/Helpers have no book)
    --prop      N     restrict to proposition number N (a PropNN folder/file); combine with --book
    --cites     NAME  row's body euclid_apply's NAME
    --depends-of NAME list what the row named NAME cites (its dependencies), EACH WITH ITS LOCATION
                      (`proposition_46 → Book/Prop46.lean:11`) so you see which book/prop it's in;
                      a name in two books shows both sources, an unindexed one shows `(not indexed)`
    --name      GLOB  fnmatch over the decl name (e.g. "proposition_29*")
    --grep      TEXT  regex over the SIGNATURE + docstring (e.g. --grep "2 \\*", --grep "△.*=.*△")

SYM is a canonical fact symbol; SOURCE FORMS are accepted and aliased: `Triangle.area`→area, `∟`→
    right_angle, `∠`→angle, `Segment.length`→length, `Point.onLine`/`a.onLine`→onLine, `=`→eq, `≠`→ne,
    `<`/`>`/`≤`/`≥`→lt/gt/le/ge. An UNKNOWN symbol ERRORS with a suggestion + the valid set (it does NOT
    silently return "no matches"). Canonical set: angle area between collinear eq ge gt insideCircle
    intersectsCircle intersectsLine isCentre le length lt ne onCircle onLine right_angle sameSide
    + the abbrevs (distinctPointsOnLine, formParallelogram, formTriangle, …).

STEPS (the 500+ Book2 stepN.lean backing files are noisy near-duplicates — HIDDEN by default):
    --steps           widen the search space to ALSO include step rows (not a selector by itself)
    --kind step       asking for steps shows them — so "browse all steps" is `--kind step`,
                      and "Prop 5's steps" is `--book 2 --prop 5 --kind step`.
    (a step row appears iff --steps is set OR the --kind set includes 'step'.)

OUTPUT: one line per match (`kind  name  source | <region>`), no row cap. A FEW results (≤5) always
print whole (a single match never clips); in a LONG list, only a GENUINELY MASSIVE line (>200 chars,
e.g. a big area-sum) is truncated with `…` — normal-length signatures show in full. Display levers:
    --show {full,conclusion,hyps}   which signature region to print — INDEPENDENT of the filter
                                    (default: the region you filtered on — concl for --concludes,
                                    hyps for --consumes, else full). So `--concludes area --show hyps`
                                    finds area-concluders but prints their hypotheses.
    --wide                          never truncate — print every match's region whole, however long.
    --json                          dump the full matching rows as JSON (the machine path).
When the result list is long the footer adds a per-book breakdown to guide narrowing.
"""
import os, re, sys, json, fnmatch, difflib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import faithful_lib as L
import bake_index as B

# MULTI-value symbol flags: repeatable AND comma-splittable, AND-ed together (every listed symbol must
# be present). Repeating one accumulates — it never silently overwrites.
_MULTI_FLAGS = {"--concludes", "--consumes", "--mentions"}
# single value flags take the next argv token (last wins).
_SINGLE_FLAGS = {"--kind", "--cites", "--depends-of", "--name", "--grep", "--book", "--prop", "--show"}
_VALUE_FLAGS = _MULTI_FLAGS | _SINGLE_FLAGS
# --steps widens the space to include step rows; --wide disables per-line truncation; --rebuild forces
# a full re-parse (find always incrementally re-bakes regardless, so there is no separate --bake).
_BARE_FLAGS = {"--steps", "--json", "--wide", "--rebuild"}
_SHOW_CHOICES = ("full", "conclusion", "hyps")


def _key(flag):
    return flag.lstrip("-").replace("-", "_")


def parse_args(argv):
    """Hand-parse argv (the repo's no-argparse convention) → an opts dict. Multi flags
    (--concludes/--consumes/--mentions) accumulate into a LIST (repeatable + comma-splittable, AND-ed);
    single flags hold their last value. Raises ValueError on an unknown flag (with a 'did you mean'
    hint) or a missing value."""
    opts = {_key(f): None for f in _SINGLE_FLAGS}
    opts.update({_key(f): [] for f in _MULTI_FLAGS})
    for f in _BARE_FLAGS:
        opts[_key(f)] = False
    i = 0
    while i < len(argv):
        a = argv[i]
        if a in _VALUE_FLAGS:
            if i + 1 >= len(argv):
                raise ValueError(f"{a} needs a value")
            val = argv[i + 1]
            if a in _MULTI_FLAGS:
                opts[_key(a)].extend(v.strip() for v in val.split(",") if v.strip())
            else:
                opts[_key(a)] = val
            i += 2
        elif a in _BARE_FLAGS:
            opts[_key(a)] = True
            i += 1
        else:
            hint = ""
            near = difflib.get_close_matches("--" + a.lstrip("-"),
                                             sorted(_VALUE_FLAGS | _BARE_FLAGS), n=1, cutoff=0.5)
            if near:
                hint = f" did you mean {near[0]}? (flags need the leading `--`)"
            raise ValueError(f"unknown argument: {a}.{hint}")
    return opts


def _polarity_query(val):
    """Split a symbol query into (canonical_symbol, required_polarity-or-None). A leading ¬ pins neg
    (`!` cannot lead — it's the alias for `ne`). The symbol is canonicalized through `L.canon_symbol`
    (so `Triangle.area`/`∟`/`Point.onLine` work) and VALIDATED against `L.VALID_SYMBOLS`; an unknown
    symbol raises ValueError naming the closest match + the valid set (main() turns it into exit 2)."""
    val = val.strip()
    pol = None
    if val.startswith("¬"):
        pol = "neg"
        val = val[1:].strip()
    sym = L.canon_symbol(val)
    if sym not in L.VALID_SYMBOLS:
        near = difflib.get_close_matches(sym, sorted(L.VALID_SYMBOLS), n=1, cutoff=0.4)
        hint = f" did you mean '{near[0]}'?" if near else ""
        raise ValueError(f"unknown symbol '{val}'.{hint} valid symbols: "
                         + ", ".join(sorted(L.VALID_SYMBOLS)))
    return sym, pol


def _has_fact(row, symbol, role, polarity):
    for f in row.get("facts", []):
        if f.get("symbol") != symbol:
            continue
        if role is not None and f.get("role") != role:
            continue
        if polarity is not None and f.get("polarity") != polarity:
            continue
        return True
    return False


def _relpath(row):
    """The row's source FILE path (the part before the `:line`)."""
    return row.get("source", "").split(":", 1)[0]


def _book_of(row):
    """The book NUMBER from a row's source path, or None. Book 1 lives under `Book/` (segment has NO
    digit → 1); Book N>1 under `BookN/`. SystemE/Helpers rows have no Book* segment → None. (Can't
    reuse faithful_lib.book_num: it raises, and it has no `Book`→1 case.)"""
    for part in _relpath(row).split("/"):
        if part == "Book":
            return 1
        m = re.fullmatch(r"Book(\d+)", part)
        if m:
            return int(m.group(1))
    return None


def _prop_of(row):
    """The proposition NUMBER from a row's source path (a `PropNN` segment or `PropNN.lean` file), or
    None if there's no Prop* component (axioms/helpers/defs)."""
    for part in _relpath(row).split("/"):
        m = re.match(r"Prop(\d+)", part)            # matches both `Prop05` (dir) and `Prop05.lean` (file)
        if m:
            return int(m.group(1))
    return None


def _int_opt(opts, key):
    """Parse a numeric filter value (e.g. --book 2) → int, or raise ValueError with a friendly message."""
    val = opts[key]
    if val is None:
        return None
    if not re.fullmatch(r"\d+", val.strip()):
        raise ValueError(f"--{key} takes a NUMBER (e.g. --{key} 2), got {val!r}")
    return int(val.strip())


def matches(row, opts):
    """True iff `row` satisfies every ACTIVE filter in `opts` (AND). Raises ValueError on a malformed
    numeric --book/--prop value."""
    if row.get("kind") == "_error":
        return False
    if opts["kind"]:
        kinds = {k.strip() for k in opts["kind"].split(",")}
        if row.get("kind") not in kinds:
            return False
    # --concludes/--consumes/--mentions are LISTS — every listed symbol must be present (AND).
    for q in opts["concludes"]:
        sym, pol = _polarity_query(q)
        if not _has_fact(row, sym, "concl", pol):
            return False
    for q in opts["consumes"]:
        sym, pol = _polarity_query(q)
        if not _has_fact(row, sym, "hyp", pol):
            return False
    for q in opts["mentions"]:
        sym, pol = _polarity_query(q)
        if not _has_fact(row, sym, None, pol):
            return False
    book = _int_opt(opts, "book")
    if book is not None and _book_of(row) != book:
        return False
    prop = _int_opt(opts, "prop")
    if prop is not None and _prop_of(row) != prop:
        return False
    if opts["cites"]:
        if opts["cites"] not in row.get("cited_props", []):
            return False
    if opts["name"]:
        if not fnmatch.fnmatch(row.get("name", ""), opts["name"]):
            return False
    if opts["grep"]:
        # search the SIGNATURE and the docstring together — so `--grep "2 \*"` / `--grep "△.*=.*△"`
        # pattern-matches the actual math, and English intent in the docstring still hits.
        hay = row.get("signature", "") + "\n" + row.get("docstring", "")
        if not re.search(opts["grep"], hay, re.IGNORECASE):
            return False
    return True


def step_allowed(row, opts):
    """Steps are hidden by default (500+ noisy near-duplicates). A step row is allowed into the result
    iff `--steps` is set OR the `--kind` set explicitly includes 'step'. Non-step rows always pass."""
    if row.get("kind") != "step":
        return True
    if opts["steps"]:
        return True
    if opts["kind"] and "step" in {k.strip() for k in opts["kind"].split(",")}:
        return True
    return False


def _default_show(opts):
    """Default projection = the region you filtered on, so it's never the part truncated away:
    --concludes → 'conclusion', --consumes → 'hyps', otherwise (incl. --mentions / both) → 'full'."""
    if opts.get("show"):
        return opts["show"]
    if opts["concludes"] and not opts["consumes"]:
        return "conclusion"
    if opts["consumes"] and not opts["concludes"]:
        return "hyps"
    return "full"


def _project(signature, show):
    """The region of `signature` to display under `show` ∈ {full,conclusion,hyps}. Uses the lib's
    paren/arrow-aware splitter; falls back to the whole signature if it can't be split."""
    if show == "full" or not signature:
        return signature
    try:
        _binders, hyps, concl, _ex = L.split_quantifier_and_arrow(signature)
    except Exception:
        return signature
    region = concl if show == "conclusion" else hyps
    region = re.sub(r"\s+", " ", region).strip()
    return region or signature                          # e.g. a hypothesis-less axiom under --show hyps


# Per-line CHARACTER budget (not terminal width). Truncation exists only to stop a GENUINELY MASSIVE
# signature (e.g. a 400-char area-sum) from swamping a scan — a normal-length line shows whole. Generous
# by design so it rarely fires.
LINE_BUDGET = 200


def render(rows, opts):
    if opts["json"]:
        print(json.dumps(rows, ensure_ascii=False, indent=2))
        return
    if not rows:
        print("[find] no matches.")
        return
    show = _default_show(opts)
    rows = sorted(rows, key=lambda r: (r.get("kind", ""), L.natural_key(r.get("name", ""))))
    namew = max(len(r.get("name", "")) for r in rows)
    # Truncate by CHARACTER, and only a MASSIVE line in a LONG list: a short result has no wall to tame,
    # so it's always shown whole (a single match never clips). `--wide` forces whole always.
    FEW = 5
    cut = not opts["wide"] and len(rows) > FEW
    truncated = 0
    for r in rows:
        region = _project(r.get("signature", ""), show)
        head = f"  {r.get('kind', ''):7} {r.get('name', ''):{namew}}  {r.get('source', '')}"
        line = head + (f"  | {region}" if region else "")
        if cut and len(line) > LINE_BUDGET:
            line = line[:LINE_BUDGET - 1] + "…"
            truncated += 1
        print(line)
    # footer: count + (when many) a per-book breakdown to GUIDE narrowing, + a truncation note.
    foot = f"[find] {len(rows)} match(es)"
    if len(rows) > 12:
        groups = {}
        for r in rows:
            groups[_group_of(r)] = groups.get(_group_of(r), 0) + 1
        foot += " — " + " ".join(f"{g}:{n}" for g, n in sorted(groups.items()))
        foot += " — narrow with --book/--prop/--grep/--kind"
    if truncated:
        foot += f"  ({truncated} line(s) truncated — --wide for complete, --show conclusion|hyps to focus)"
    print(foot)


def _group_of(row):
    """A coarse location bucket for the footer breakdown: BookN / SystemE / Helpers / other."""
    rel = row.get("source", "")
    b = _book_of(row)
    if b is not None:
        return f"Book{b}"
    top = rel.split("/", 1)[0]
    return top or "?"


def main(argv):
    try:
        opts = parse_args(argv)
    except ValueError as e:
        print(f"[find] {e}\n")
        print(__doc__)
        return 2

    if opts["show"] is not None and opts["show"] not in _SHOW_CHOICES:
        print(f"[find] --show takes one of {', '.join(_SHOW_CHOICES)} (got {opts['show']!r}).")
        return 2

    all_rows, _ = B.ensure_fresh(force=opts["rebuild"])

    # --depends-of NAME: print that decl's cited_props (its foundation), then done.
    if opts["depends_of"]:
        hits = [r for r in all_rows if r.get("name") == opts["depends_of"]]
        if not hits:
            print(f"[find] no declaration named '{opts['depends_of']}'.")
            return 1
        # name → [source, …] so each citation can be shown WITH its location (a bare name may resolve
        # to >1 row — e.g. `proposition_5` is in both books — so we show every source, not just one).
        sources_of = {}
        for row in all_rows:
            if row.get("kind") != "_error":
                sources_of.setdefault(row.get("name"), []).append(row.get("source", "?"))
        for r in hits:
            deps = r.get("cited_props", [])
            print(f"  {r['name']}  ({r['source']}) cites:" + ("" if deps else " (nothing)"))
            width = max((len(d) for d in deps), default=0)
            for d in deps:
                locs = sources_of.get(d)
                loc = " | ".join(locs) if locs else "(not indexed)"
                print(f"      {d:{width}}  →  {loc}")
        return 0

    # A SELECTOR narrows the rows; --steps is only a space-widener, NOT a selector (so `--steps` alone
    # is rejected — point the user at `--kind step` to browse steps).
    active = any(opts[k] for k in ("concludes", "consumes", "mentions", "kind",
                                   "book", "prop", "cites", "name", "grep"))
    if not active:
        print("[find] no selector given — specify at least one of --concludes/--consumes/--mentions/"
              "--kind/--book/--prop/--cites/--depends-of/--name/--grep. (To browse step files, use "
              "`--kind step`; `--steps` only WIDENS another query to include steps.)\n")
        print(__doc__)
        return 2

    try:
        out = [r for r in all_rows if matches(r, opts) and step_allowed(r, opts)]
    except ValueError as e:
        print(f"[find] {e}")
        return 2
    render(out, opts)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except L.FaithfulError as e:
        print(f"[find] {e}")
        sys.exit(1)
