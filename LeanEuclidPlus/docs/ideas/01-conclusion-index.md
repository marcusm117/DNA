# 01 — Fact database + multi-axis query tool (`bake_index` + `find`)

**Status:** idea · **Serves:** #1 (reasoning), #2 (search), #5 (reuse) · **Effort:** medium · **Priority:** 1st (keystone)

> **Design correction (don't lose this):** this is NOT a "conclusion index." It's a COMPLETE structured
> database of every declaration, queryable along MANY axes. "What concludes X" is just ONE query. The DB
> is dumb and complete; the *queries* carry the intelligence. Bake once (richly) → query infinitely many
> ways → add new query modes later WITHOUT re-baking.

## Problem it solves

To make progress the agent must answer questions like: "what gets me `parallel`?", "I HAVE a
parallelogram — what can I do with it?", "what are ALL the axioms about `intersectsLine` (how does this
opaque def even behave)?". Today it reads `SystemE/Theory/Inferences/*.lean` or greps (which the bash hook
blocks), then guesses signatures. That's search tokens + wrong-axiom build attempts + re-think loops.

## Why it helps (in cost terms)

- **#2 search:** one query returns candidates instead of the agent reading theory files.
- **#5 reuse:** proven props + (opt-in) per-steps live in the same DB — "proved before?" is the same query.
- **#1 reasoning — the underrated win:** the hard part isn't the prose, it's "what are my legal MOVES?"
  The DB turns open derivation into **menu-picking** (forward AND backward — see below), which is a
  fraction of the tokens and stops the agent committing to approaches no axiom supports.

## The three query DIRECTIONS (all over ONE database)

1. **Backward — "what CONCLUDES this?"** (`--concludes "¬intersectsLine"`): I want `parallel`; what gets
   me there? → filter rows where the symbol appears in the CONCLUSION (with polarity).
2. **Forward — "what CONSUMES this?"** (`--consumes formParallelogram`): I HAVE a parallelogram; what can I
   DO with it? → filter rows where the symbol appears in a HYPOTHESIS. (This is how you reason FORWARD from
   facts you already have — arguably more valuable for #1 than backward, and the axis I originally missed.)
3. **Filter / browse by attribute** (`--mentions intersectsLine --kind axiom`): everything touching a
   symbol, anywhere, filtered by kind/source. KEY INSIGHT: for an `opaque` def like `intersectsLine`, **the
   set of axioms that MENTION it IS its definition** — so "understand the opaque def" is just this query
   filtered to axioms, not a separate feature.

All three are filters over the same rows. Combine freely (`--consumes X --concludes Y --kind helper`).

### More angles (all still over the SAME rows — the lesson is "bake more per row, not build more tools")

4. **By citation / dependency, BOTH directions:** `--cites proposition_30` (what USES Prop30 → worked
   examples + feeds the faithful dependency check) and `--depends-of helper_…` (what a decl cites → its
   foundation). Needs the bake to record each decl's `euclid_apply (X …)` calls. Not just props — anything.
5. **By name pattern / family:** `--name "proposition_29*"` returns the whole `29 / 29' / 29'' / 29'''''`
   family side-by-side with their DIFFERING signatures — kills the "picked the wrong prime" failed-wire loop.
6. **Full-text / docstring search:** `--grep "repackaged from"` over the English docstrings every helper/step
   carries. This is the closest to SEARCH-BY-INTENT without AI — find something when you know what it's FOR
   but not its symbol shape.

> **Bake-everything principle:** the answer to "what other angles?" is record more PER ROW, not build more
> tools. Parsing is free and the jsonl is never read whole, so bake every cheaply-extractable attribute NOW
> even if no query uses it yet — under-baking forces a re-bake later. So each row ALSO carries: `hyp_count`,
> `cited_props` (the `euclid_apply (proposition_…)`/helper calls in the body), `docstring` text, `raw_name`,
> `object_arity`. Known CEILING (record, don't fake): "find a lemma with a SIMILAR PROOF TECHNIQUE" (not
> symbols, not text — strategy similarity) needs AI or hand-tags; out of scope for the mechanical tool.

See [09](09-next-move-ranking.md) for the highest-value query that builds on this DB + the agent's live
context: "rank candidates by how many hyps are ALREADY satisfied" (cheapest next move).

## Sketch

- **`scripts/bake_index.py`** — PURE PARSE, no Lean, no builds, sub-second. Emits `index.jsonl`, one row
  per declaration, recording the FULL structure (so any future query axis is already supported):
  ```
  {kind: axiom|def|helper|prop|step,
   name, source: "path:line",
   signature,                         # human-readable, for the agent to read
   facts: [ {symbol: "intersectsLine"|"sameSide"|"formParallelogram"|"between"|"onLine"|"area"|"right_angle"|…,
             role: hyp|concl,
             polarity: pos|neg} , … ] # EVERY geometric relation the decl touches, with where + sign
   hyps: [...full atomic hyp types...],
   # bake-everything (cheap to extract, enables future angles without re-bake):
   hyp_count, cited_props: [...euclid_apply'd props/helpers...], docstring, raw_name, object_arity }
  ```
  The `facts` list (symbol × role × polarity) is what makes all three directions queryable from one bake.
- **`scripts/find.py`** — filters and returns ONLY matching rows (token discipline: the jsonl can be huge;
  the agent never reads it whole). Flags: `--concludes`, `--consumes`, `--mentions`, `--kind`, `--prop`,
  combinable.
- **Freshness — INCREMENTAL auto-bake on every query.** `find.py` re-parses only mtime/hash-changed
  `.lean` files (common case = a no-op stat check), so "auto-bake every query" stays free; removes the
  "forgot to rebake" risk; makes a write-hook unnecessary. Plus a manual **`--bake` / `--rebuild`** for
  first run or a massive change (full re-parse).

## Step display tiering (steps are noisy — many duplicates)

```
default       → axioms + helpers + props        (NO steps)
--steps       → + steps of the CURRENT prop only (cheap live reuse)
--steps-all   → every step everywhere           (explicit, rare — really for the promotion miner [03])
```
The duplication that makes `--steps-all` noisy is itself the promotion signal ([03](03-promotion-miner.md)).

## Open questions / risks

- **The ceiling of "smart but no AI":** symbol+role+polarity filtering handles all the examples above
  cleanly, but FUZZY/semantic ("like this but not exact") is beyond non-AI search — by design. ESCAPE
  HATCH: queries narrow to a handful; the AGENT does the final semantic match by reading ~5 candidates,
  not 500. Tool narrows mechanically; existing agent intelligence does the fuzzy last step. No AI in the tool.
- **Step payload: signature+path, NOT full body** (full bodies bloat every result). Generic steps (e.g.
  `Book2/Prop02/step5_hsq.lean`) are the exception → PROMOTE to `Helpers/` and index as helpers.
- **`facts` extraction:** robust parse of each relation's head symbol + role + polarity across goal shapes
  (negation, `≠` as `¬ =`, abbrevs like `formParallelogram`). Abbrevs may need a head category or unfolding.
- **Hook constraint:** `find.py` / `bake_index.py` must be added to the bash allowlist (new `scripts/…`).
