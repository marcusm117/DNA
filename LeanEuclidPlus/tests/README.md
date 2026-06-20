# `tests/` — parse-only sanity tests for the fact-database tooling

Covers `bake_index.py` + `find.py` + the parse helpers they added to `faithful_lib.py` (the "idea 01"
declaration database / smart-grep). These are **pure-parse** tests — no Lean, no `lake`, no SMT — so
they run in milliseconds against tiny static `.lean` snippets under `fixtures/`. They do NOT touch the
real `.lake/index.jsonl` (the freshness test monkeypatches `bake_index`'s paths to a tmp dir).

## Running

From `LeanEuclidPlus/` (bare — `python3 -m pytest` is on the allowlist):

```
python3 -m pytest tests/
```

`conftest.py` puts `scripts/` on `sys.path` so the tests import `faithful_lib` / `bake_index` / `find`
the same way the scripts import each other.

## Dependency

`pytest` (dev only — not needed by the proving pipeline). Install once into whatever `python3`
resolves to when you run the bare allowlisted command:

```
python3 -m pip install pytest
```

## What each module checks

| File | Focus |
|------|-------|
| `test_split.py` | `split_signature` / `split_quantifier_and_arrow` / `split_conjuncts` / `parse_binders` — ∀-peel, top-level `→` split, `∃` strip, curried binders |
| `test_facts.py` | `extract_facts` — symbol × role × polarity; `¬`→neg; `≠`→`ne`/neg (incl. inside parens); metric `∠…=∟`→ angle+right_angle+eq |
| `test_abbrev.py` | abbrev unfolding (packaged + `via`-tagged atoms; negated abbrev packaged-only); registry-vs-`Relations.lean` drift guard |
| `test_citations.py` | `cited_in_body` — prop/construction/helper heads, dedup, comment-safe |
| `test_bake_row.py` | `bake_index.parse_file` — full row schema, `concludes_exists`, prime families, classification, no `_error` rows |
| `test_find.py` | `find.matches` / `step_visible` / `parse_args` — every filter + AND-combination + step tiering |
| `test_freshness.py` | `ensure_fresh` — incremental re-parse of only changed files; removed files drop rows; schema-bump forces rebuild |
