# 01 (+09) — Fact database + multi-axis query tool (`bake_index` + `find`)

> **STATUS UPDATE (Phase 1 BUILT):** `scripts/bake_index.py` + `scripts/find.py` are implemented and
> tested (`tests/`, pure-parse, 38 cases). All Phase-1 query axes work: `--concludes`/`--consumes`/
> `--mentions` (symbol×role×polarity, `¬`-prefix for negation), `--cites`/`--depends-of`, `--name`
> glob, `--grep` docstring, numeric `--book`/`--prop` location filters, step gating (`--kind step` to
> browse, `--steps` to widen another query), incremental auto-bake. The index
> lives at `.lake/index.jsonl` (git-ignored). The merged **idea-09 "cheapest next move" ranker is NOT
> built yet** — it's deferred (needs a live `check_step --context` build + first-order matcher); Phase 1
> already bakes BOTH packaged + unfolded abbrev facts so 09 can be added with no re-bake. `find.py` is
> wired into the bash allowlist + CLAUDE.md as the sanctioned smart-grep.

**Status:** idea · **Serves:** #1 (reasoning), #2 (search), #5 (reuse) · **Effort:** medium · **Priority:**
Program 1 (REUSE) — the DB/search half. **`find.py` is the sanctioned smart-grep** (give the agent this
instead of re-allowing raw `grep`). Idea 09 ("cheapest next move") is MERGED in below — it's a query MODE
of this same DB, not a separate idea.

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

The highest-value query — "rank candidates by how many hyps are ALREADY satisfied" (cheapest next move) —
is MERGED into this file below (was idea 09); it builds on this DB + the agent's live context.

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

The 500+ Book2 `stepN.lean` rows are near-duplicates, so they're HIDDEN by default. As built, step
visibility is decoupled from a *location* filter (the original `--steps-all` / path-`--prop` coupling
was confusing — a bare `--steps` couldn't even run). The shipped semantics:
```
default                       → axioms + helpers + props + defs   (NO steps)
--kind step                   → browse ALL step rows              (asking for steps shows them)
--book N --prop M --kind step → that prop's steps                 (location is a separate numeric filter)
--steps                       → WIDEN any other query to also include step rows (not a selector itself)
```
Location filtering is the general numeric `--book N` / `--prop M` (independent, combinable), NOT a
step-only scope. The duplication that makes the full step set noisy is itself the promotion signal
([03](03-promotion-miner.md)).

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

---

## 09 (MERGED) — "Cheapest next move": rank candidates by how much is already in context

> This was a separate idea; it is the FLAGSHIP query of the DB above + the agent's CURRENT CONTEXT + a
> matcher + cost ranking. It answers "what's my best LEGAL MOVE given THIS proof state," not just "what
> exists." Serves #1 (reasoning) and #2 (search). The most decision-relevant query the DB enables.

### Problem it solves

The DB answers "what concludes/consumes/mentions X." But the agent's real question at a node is:
**"given the atoms I ALREADY have in context, which lemma gets me to my goal with the LEAST additional
work?"** A lemma whose 5 hyps are all already in context is a free win; one needing 3 new sub-proofs is
expensive. Today the agent can't see that ranking — it picks a lemma, then discovers mid-wire how many
hyps it can't supply.

### Sketch

1. **Get context:** the pipeline already produces it — `check_step --context <node>` (trace_state) lists
   the ground atoms in scope. Feed those to the query.
2. **Candidate set:** from the DB, the lemmas/axioms/props whose CONCLUSION matches the goal shape (backward).
3. **Match each candidate's hyps against context — FIRST-ORDER MATCHING (the crux):**

   **Phase A — conclusion pins (always unambiguous).** The agent has already decided its claim via SF
   before it ever queries — the goal is a FULLY GROUND atom with real figure names (`¬(b.onLine EF)`,
   not a wish). Matching the lemma conclusion against that goal is deterministic: each syntactic position
   in the conclusion binds exactly one hole (`¬(x.onLine M)` → `{x→b, M→EF}`). No symmetry concern,
   no ambiguity. This is by design — SF precedes search.

   **Phase B — hyp search over remaining free variables.** After Phase A, some lemma args are bound;
   the rest are FREE (not mentioned in the conclusion). For each free variable, the search space is
   "which context atom of the right type to assign it." This is the only real search:
   - For each unbound free var, try every same-type context atom.
   - Extend ONE CONSISTENT substitution across all hyps — if hyp₁ forces `L→AB` and hyp₂ forces
     `L→CE`, reject that branch immediately.
   - Goal: find the assignment that **minimizes unsatisfied hyps** (not just "find any match") →
     needs branch-and-bound: keep running best, prune branches whose partial lower bound already
     exceeds current best.

   **Why it's cheap.** Let m = number of free variables REMAINING after Phase A, c = context size
   (~10–20 atoms). Worst case is c^m — NOT n! (factorial would be permutations; this is just
   assignment). Consistency pruning shrinks the branching factor at each depth (once `L→AB` is
   committed, every subsequent hyp with `L` checks in O(1) — no re-search). In practice m ≤ 3–4 for
   these figure lemmas, so the real search tree is tens to hundreds of nodes — sub-millisecond
   exhaustive search.

   - Count hyps that CAN'T be matched under the best consistent assignment = "still to prove."

4. **Rank ascending by (hyps-still-to-prove).** Output: candidate, the substitution, which hyps are already
   satisfied, which remain. Cheapest-to-apply first.

### Syntactic matching vs. logical equivalence — the deliberate choice

- **Pure string equality:** too weak — fails on variable renaming (lemma `x.onLine L` vs context
  `b.onLine AB`). REJECTED.
- **First-order matching (up to variable assignment):** handles renaming, deterministic, cheap, no SMT/AI.
  CHOSEN level.
- **Full logical equivalence (SMT):** too expensive, overkill.
- **The GAP and why it's SAFE:** matching misses SEMANTIC equivalence — distance symmetry `|a─b|=|b─a|`,
  `intersectsLine` orientation, packaged-vs-unfolded abbrevs (`formParallelogram`). A hyp present
  up-to-symmetry is counted "unmatched." But that only makes a candidate look MORE expensive than it is —
  it NEVER yields a false "free" match or a wrong wire. So it's a SOUND, conservative ranking heuristic; the
  cost estimate is pessimistic, which is the safe bias. (If symmetry-blindness ever hurts ranking quality
  noticeably, add a few normalization rules — canonicalize distance/angle arg order, unfold known abbrevs to
  atoms — BEFORE matching. Cheaper than SMT, closes most of the gap.)

### Open questions / risks (09-specific)

- **Abbrev unfolding:** `formParallelogram` in a hyp is really a conjunction of atoms; decide whether to
  match against the packaged form or the unfolded atoms (the context usually has it UNFOLDED — so unfold
  candidate hyps too, or match at the atom level).
- **Context source coupling:** depends on `--context`'s trace_state. Fine (it exists), but means this query
  runs a (cheap) build to get context, unlike the pure-parse DB queries. Acceptable — builds are free.
- **Ranking ties:** many candidates may tie on hyp-count; secondary sort by total hyps, or by `kind`
  (prefer helper/axiom over re-deriving). Tune empirically.
