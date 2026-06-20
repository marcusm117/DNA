#!/usr/bin/env python3
"""Bake a structured, parse-only FACT DATABASE of every System-E declaration → `.lake/index.jsonl`.

This is the DB half of "idea 01" (docs/ideas/01-conclusion-index.md): a COMPLETE, dumb, structured
record of every axiom / def / abbrev / opaque pred / proposition / helper / step, one JSON row per
declaration. The intelligence lives in the QUERIES (`find.py`), not here — so this bakes RICHLY (every
cheaply-extractable attribute) once, and any future query axis is already supported without a re-bake.

PURE PARSE — no Lean, no builds, sub-second. Each row records:
    kind, name, raw_name, source ("relpath:line"), signature, docstring, object_arity, hyp_count,
    hyps (verbatim conjuncts), facts ([{symbol, role:hyp|concl, polarity:pos|neg, raw, via}]),
    cited_props (euclid_apply'd names in the body), concludes_exists.
The `facts` list (symbol × role × polarity) is what lets `find.py` answer "what CONCLUDES / CONSUMES /
MENTIONS X" off this one bake.

USAGE (run BARE from LeanEuclidPlus/, never piped):
    python3 scripts/bake_index.py                 # incremental: re-parse only changed .lean files
    python3 scripts/bake_index.py --rebuild        # full re-parse from scratch (first run / schema bump)
    python3 scripts/bake_index.py --json           # also emit a one-line JSON summary to stdout

`find.py` calls `ensure_fresh()` itself on every query, so you rarely run this by hand — it's here for
the first bake, a forced rebuild, or to see the per-kind row counts.
"""
import os, re, sys, glob, json, fcntl

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import faithful_lib as L

SCHEMA = 2                                          # bump ⟹ ensure_fresh() forces a full rebuild
INDEX_PATH = os.path.join(L.BOOK_ROOT, ".lake", "index.jsonl")
MANIFEST_PATH = os.path.join(L.BOOK_ROOT, ".lake", "index.manifest.json")
LOCK_PATH = os.path.join(L.BOOK_ROOT, ".lake", "index.lock")

# The file globs we index (relative to BOOK_ROOT). Shared with find.py via scan_targets().
TARGET_GLOBS = (
    "SystemE/Theory/Relations.lean",
    "SystemE/Theory/Inferences/*.lean",
    "SystemE/Theory/Constructions/*.lean",
    "Book/Prop*.lean",
    "Book2/*/Main.lean",
    "Book2/*/step*.lean",
    "Helpers/*.lean",
)

# A declaration head: a keyword + name, up to the `:` that starts its type. `opaque`/`abbrev`/`def`
# may use `:=` or a `Sort`-arrow form; we capture the keyword + name + the rest of the line region and
# let the per-kind logic carve the type. Names keep trailing primes (proposition_29'') and subscripts.
DECL_HEAD = re.compile(r"^[ \t]*(axiom|theorem|lemma|opaque|abbrev|def)\s+([A-Za-z_][\w'.]*)", re.MULTILINE)


def scan_targets():
    """Absolute paths of every .lean file we index, de-duplicated and sorted."""
    out = set()
    for g in TARGET_GLOBS:
        out.update(glob.glob(os.path.join(L.BOOK_ROOT, g)))
    return sorted(out)


def _rel(path):
    return os.path.relpath(os.path.realpath(path), L.BOOK_ROOT)


def _line_of(src, off):
    """1-based line number of character offset `off`."""
    return src.count("\n", 0, off) + 1


def _docstring_above(src, head_start):
    """The `/-- … -/` or `/- … -/` doc-comment block immediately above the decl head at `head_start`
    (only whitespace allowed between the block's close and the head). Returns the inner text stripped,
    or "" if none. Read from the ORIGINAL source so the doc text survives (we never blank it here)."""
    pre = src[:head_start]
    m = re.search(r"/-(-?)(.*?)-/\s*$", pre, re.DOTALL)
    if not m:
        return ""
    return re.sub(r"\s+", " ", m.group(2)).strip()


def _header_and_body(clean, type_start, kind, next_start):
    """Carve a declaration's HEADER (binders + type, between name and the proof `:=`/end) and BODY
    (after `:=`; theorems/defs/abbrevs only). Slices the COMMENT-BLANKED copy `clean` so trailing
    `-- …` notes between this decl's end and the next decl head never leak into the signature/facts
    (comments are spaces in `clean`, collapsed later). `type_start` is just after the name; `next_start`
    bounds this decl (the next decl head or EOF). Returns (header_text, body_text)."""
    if kind in ("theorem", "lemma", "def", "abbrev"):
        sep = _top_level_assign(clean, type_start, next_start)   # proof/value separator = first top `:=`
        if sep is not None:
            return clean[type_start:sep].strip(), clean[sep + 2:next_start]
        return clean[type_start:next_start].strip(), ""
    # axiom / opaque: no `:=` body — the whole region after the name is the type/signature
    return clean[type_start:next_start].strip(), ""


def _top_level_assign(clean, start, end):
    """Index of the first top-level `:=` in clean[start:end] (paren/bracket/string aware), or None."""
    depth, i = 0, start
    while i < end:
        c = clean[i]
        if c == '"':
            i = L._skip_string(clean, i, end); continue
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and clean.startswith(":=", i):
            return i
        i += 1
    return None


def classify(kind_kw, name, path):
    """Map a decl keyword + name + file to the row `kind`. `prop` and `step` are the refinements:
      - prop : name matches `proposition_<n>` (any trailing primes), in Book/ or Book2/*/Main.lean.
      - step : a `helper_…` theorem living in a `Book*/Prop*/stepN.lean` backing file.
      - helper: any other `helper_…`, or any theorem under Helpers/.
    Otherwise the keyword itself (axiom/def/abbrev/opaque/theorem)."""
    rel = _rel(path)
    if kind_kw in ("theorem", "lemma"):
        if re.fullmatch(r"proposition_\d+'*", name):
            return "prop"
        if name.startswith("helper_"):
            # under Book*/PropNN/stepN.lean ⟹ step; under Helpers/ ⟹ helper
            if re.search(r"/Book\d+/Prop\d+/", "/" + rel) and os.path.basename(path).startswith("step"):
                return "step"
            return "helper"
        if rel.startswith("Helpers/"):
            return "helper"
        return "theorem"
    return kind_kw


def _namespace_of(src, head_start):
    """The innermost `namespace …` opened before `head_start` (minus any closed by an `end`). Used to
    build raw_name. Cheap last-open-wins scan on a comment-blanked copy."""
    clean = L.blank_comments(src[:head_start])
    ns = []
    for m in re.finditer(r"^[ \t]*(namespace|end)\b[ \t]*([\w.]*)", clean, re.MULTILINE):
        if m.group(1) == "namespace":
            ns.append(m.group(2))
        elif ns:
            ns.pop()
    return ".".join(n for n in ns if n)


def bake_decl(src, clean, m, next_start, path):
    """Build one index row for the declaration whose head `m` matched in `src`. `clean` is the
    comment-blanked copy; `next_start` is where the following decl (or EOF) begins."""
    kind_kw, name = m.group(1), m.group(2)
    type_start = m.end()
    header, body = _header_and_body(clean, type_start, kind_kw, next_start)
    binders_text, type_text = L.split_signature(header)
    # props/axioms carry their binders inside a leading `∀ (…)`; helpers carry them curried before `:`.
    qb, hyps_text, concl_text, concludes_exists = L.split_quantifier_and_arrow(type_text)
    all_binders_text = (binders_text + " " + qb).strip()
    binders = L.parse_binders(all_binders_text)
    object_arity = sum(len(idents) for idents, btype in binders if btype in L.SORT_TYPES)

    hyp_conjuncts = L.split_conjuncts(hyps_text)
    # hypothesis binders (Prop-typed curried binders, e.g. helper `(hfbc : ∠…=∟)`) are ALSO hyps
    hyp_binder_types = [btype for idents, btype in binders
                        if btype and btype not in L.SORT_TYPES for _ in idents]
    facts = L.extract_facts(hyps_text, "hyp")
    for bt in hyp_binder_types:                      # treat each hyp-binder's type as a hyp region too
        facts.extend(L.extract_facts(bt, "hyp"))
        hyp_conjuncts.append(bt.strip())
    facts.extend(L.extract_facts(concl_text, "concl"))

    kind = classify(kind_kw, name, path)
    ns = _namespace_of(src, m.start())
    return {
        "kind": kind,
        "name": name,
        "raw_name": f"{ns}.{name}" if ns else name,
        "source": f"{_rel(path)}:{_line_of(src, m.start())}",
        "signature": re.sub(r"\s+", " ", type_text).strip(),
        "docstring": _docstring_above(src, m.start()),
        "object_arity": object_arity,
        "hyp_count": len(hyp_conjuncts),
        "hyps": hyp_conjuncts,
        "facts": facts,
        "cited_props": L.cited_in_body(body) if body else [],
        "concludes_exists": concludes_exists,
    }


def parse_file(path):
    """Every index row in one .lean file (in source order). Robust per-decl: a parse error in one
    declaration is recorded as an `_error` row rather than aborting the whole file."""
    src = open(path, encoding="utf-8").read()
    clean = L.blank_comments(src)
    heads = list(DECL_HEAD.finditer(clean))
    rows = []
    for idx, m in enumerate(heads):
        nxt = heads[idx + 1].start() if idx + 1 < len(heads) else len(src)
        try:
            rows.append(bake_decl(src, clean, m, nxt, path))
        except (L.FaithfulError, ValueError, IndexError) as e:
            rows.append({"kind": "_error", "name": m.group(2), "source": f"{_rel(path)}:{_line_of(src, m.start())}",
                         "error": str(e), "signature": "", "docstring": "", "facts": [], "hyps": [],
                         "cited_props": [], "object_arity": 0, "hyp_count": 0, "concludes_exists": False,
                         "raw_name": m.group(2)})
    return rows


# ── freshness: incremental re-parse of only changed files ─────────────────────────────────────────────
def _read_manifest():
    try:
        with open(MANIFEST_PATH, encoding="utf-8") as f:
            m = json.load(f)
        return m if isinstance(m, dict) else {}
    except (OSError, ValueError):
        return {}


def _read_index():
    """Load index.jsonl → list of rows. Returns [] if absent/unreadable."""
    if not os.path.exists(INDEX_PATH):
        return []
    rows = []
    try:
        with open(INDEX_PATH, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line:
                    rows.append(json.loads(line))
    except (OSError, ValueError):
        return []
    return rows


def _write_index(rows, manifest):
    os.makedirs(os.path.dirname(INDEX_PATH), exist_ok=True)
    tmp = INDEX_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    os.replace(tmp, INDEX_PATH)
    tmp = MANIFEST_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, sort_keys=True)
    os.replace(tmp, MANIFEST_PATH)


def _file_meta(path):
    st = os.stat(path)
    return {"mtime": st.st_mtime, "sha": None}          # sha filled lazily only when mtime changed


def ensure_fresh(*, force=False, verbose=False):
    """Bring `.lake/index.jsonl` up to date with the .lean files on disk, re-parsing ONLY files whose
    mtime/sha changed (or everything when `force`). Returns (rows, changed_count). Cheap no-op when
    nothing changed (a stat per file). Serialized by a flock so two concurrent `find.py` runs never
    write a half-baked index."""
    os.makedirs(os.path.dirname(LOCK_PATH), exist_ok=True)
    with open(LOCK_PATH, "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        manifest = _read_manifest()
        targets = scan_targets()
        target_rels = {_rel(p) for p in targets}
        schema_ok = manifest.get("_schema") == SCHEMA
        if force or not schema_ok:
            rows, changed = [], 0
            files_meta = {}
            for p in targets:
                rows.extend(parse_file(p))
                fm = _file_meta(p); fm["sha"] = L.file_sha(p)
                files_meta[_rel(p)] = fm; changed += 1
            _write_index(rows, {"_schema": SCHEMA, "files": files_meta})
            if verbose:
                print(f"[bake_index] full {'rebuild' if force else '(schema bump)'}: "
                      f"{len(rows)} rows from {changed} files.", flush=True)
            return rows, changed

        old_files = manifest.get("files", {})
        rows = _read_index()
        by_file = {}
        for r in rows:
            by_file.setdefault(r["source"].split(":", 1)[0], []).append(r)

        changed_rels = []
        new_meta = dict(old_files)
        for p in targets:
            rel = _rel(p)
            prev = old_files.get(rel)
            st = os.stat(p)
            if prev and abs(prev.get("mtime", -1) - st.st_mtime) < 1e-6:
                continue                                # mtime unchanged → trust it (no hash)
            sha = L.file_sha(p)
            if prev and prev.get("sha") == sha:
                new_meta[rel] = {"mtime": st.st_mtime, "sha": sha}   # touched but identical: refresh mtime
                continue
            changed_rels.append(rel)
            new_meta[rel] = {"mtime": st.st_mtime, "sha": sha}
        removed_rels = [rel for rel in old_files if rel not in target_rels]

        if not changed_rels and not removed_rels:
            if any(new_meta[r]["mtime"] != old_files[r]["mtime"] for r in old_files if r in new_meta):
                _write_index(rows, {"_schema": SCHEMA, "files": new_meta})   # persist refreshed mtimes
            if verbose:
                print(f"[bake_index] up to date: {len(rows)} rows, 0 files re-parsed.", flush=True)
            return rows, 0

        for rel in removed_rels:
            by_file.pop(rel, None)
            new_meta.pop(rel, None)
        for rel in changed_rels:
            by_file.pop(rel, None)
            by_file[rel] = parse_file(os.path.join(L.BOOK_ROOT, rel))
        merged = [r for rel in sorted(by_file) for r in by_file[rel]]
        _write_index(merged, {"_schema": SCHEMA, "files": new_meta})
        if verbose:
            print(f"[bake_index] incremental: re-parsed {len(changed_rels)} changed, "
                  f"dropped {len(removed_rels)} removed → {len(merged)} rows.", flush=True)
        return merged, len(changed_rels) + len(removed_rels)


def _summary(rows):
    counts = {}
    for r in rows:
        counts[r["kind"]] = counts.get(r["kind"], 0) + 1
    return counts


def main(argv):
    force = "--rebuild" in argv or "--force" in argv
    as_json = "--json" in argv
    unknown = [a for a in argv if a not in ("--rebuild", "--bake", "--json", "--force")]
    if unknown:
        print(f"[bake_index] unknown args: {unknown}\n", end="")
        print(__doc__)
        return 2
    rows, changed = ensure_fresh(force=force, verbose=True)
    counts = _summary(rows)
    errs = counts.get("_error", 0)
    pretty = ", ".join(f"{k}={counts[k]}" for k in sorted(counts) if k != "_error")
    print(f"[bake_index] {len(rows)} rows ({pretty})"
          + (f"  ⚠ {errs} parse error rows" if errs else "")
          + f"  → {os.path.relpath(INDEX_PATH, L.BOOK_ROOT)}")
    if as_json:
        print(json.dumps({"rows": len(rows), "changed_files": changed, "counts": counts}))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except L.FaithfulError as e:
        print(f"[bake_index] {e}")
        sys.exit(1)
