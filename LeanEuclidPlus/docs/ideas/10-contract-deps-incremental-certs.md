# 10 — Explicit named dependencies + contract-hash incremental certificates

**Status:** idea (actively developing) · **Serves:** #3, #4 (+ #1/#5 clarity) · **Effort:** med-high
(staged) · **Priority:** high — it closes a real false-confidence hole AND unlocks "certify once, never
re-audit"

## The bug that triggered this

On Prop05, `check_step Book2/Prop05 --subtree step7` PASSED but `--all` FAILED (a real, deterministic
zero-SMT `assumption` failure deep under `step7_dfpar_boffDG`). That looks like a contradiction — "subtree
of a node should be a slice of `--all`" — but it isn't a bug:

- `--subtree X` audits **Cone(X)** = X + the sub-`have`s *physically inside X's backing file*
  (`cone_names`/`_containment` in `faithful_lib.py`).
- `step7` is a **leaf** (`step7.lean` body is `euclid_intros; euclid_apply …; euclid_apply …;
  euclid_finish`, no sub-`have`s) → `Cone(step7) = {step7}`. So `--subtree step7` certified almost nothing.
- `step7`'s REAL prerequisites — `step7_dfpar`, `step7_cmpar`, `step7_lhm`, `step7_dhg`, `step7_bmf`,
  `step6` — are **dependency siblings**: Main-level nodes whose CLAIMS are handed to `step7` as hypothesis
  binders (`hdfpar : formParallelogram …`, etc.). The containment graph has **no edge** for these, so
  `--subtree` never follows them. The shared `step7_` name prefix is a mnemonic, NOT containment.

**Root cause:** a leaf-with-hypotheses depends on facts by *value supplied at the wire*, and that
dependency is invisible to every tool — it's discharged anonymously by `(by assumption)` against whatever
the parent context happens to hold. We have no machine-readable record of *what a node consumes* or *who
produces it*.

## The idea, in one line

Make a node's dependencies **explicit and checked-by-Lean** by discharging each hypothesis with the
**name of its producer** instead of an anonymous `(by assumption)` — turning the dependency graph from an
invisible runtime fact into a static, audited invariant. Then certificates can key on a dependency's
**contract (claim type)** rather than its file, so "step X is complete" survives forever until X's own
source or one of X's declared dependencies' *contracts* changes.

## Part A — explicit named dependencies (`@deps`)

The faithful pipeline already names every node (`have step7_dfpar : … := by sorry`). So `step7`'s
hypothesis `hdfpar` can be discharged by the **term** `step7_dfpar` (the producing node's name) — and
`euclid_apply` already takes hypothesis args as terms (`(by assumption)` *is* a term). So the minimal
change needs **no new tactic**:

```
-- now (anonymous, opaque provenance):
euclid_apply (helper_2_5_step7 c d b … (by assumption) (by assumption) …)
-- proposed (named producers — the @deps list IS the hypothesis args):
euclid_apply (helper_2_5_step7 c d b … step7_dfpar step7_cmpar step6 …)
```

`wired_body` swaps `["(by assumption)"] * n_hyps` for the declared producer names. Lean's elaboration
becomes the check: wrong name → `unknown identifier`; wrong/reoriented type → type error. Because the
arg list *is* the dependency declaration, there's no separate `--check` coverage to maintain and **no
annotation that can silently drift from reality**.

(If a fact is one you'd rather not pin to a single producer, a custom `assumption_from [h1, h2]` tactic
— `first | exact h1 | exact h2 | fail` — is ~20 lines and SystemE already has the tactic infra. Reach for
pass-by-name first.)

### Why this is a correctness gain, not just clarity

Plain `assumption` can discharge a hyp from *any* coincidentally type-matching context fact, so a missing
or wrong producer gets **silently masked** by an unrelated fact. Named discharge makes `step7` **fail
loudly** if `step7_dfpar` is absent or off — exactly the bug class above. It also removes ambiguity when
several facts could match, and makes "what is used where" readable straight off the wire (serves reasoning
#1 and reuse #5).

### The hybrid is the realistic shape (and matches "lazy → list all → only `--all`")

Not every hyp traces to a named node — some are proposition premises (`euclid_intros`) or constructions
(`… as h …`, which *are* named), and some are unnamed SMT-derived context facts. So each hyp arg is
**either a declared name or `(by assumption)`**. The named ones are provenance-clear and node-scoped-
auditable; the `(by assumption)` remainder is the opaque set that **only `--all` covers**. That is
precisely the current all-or-nothing behavior, refined to per-hypothesis granularity: a lazy agent that
names nothing falls back to today's "container is the unit, `--all` checks everything."

## Part B — `--node-complete X` (sound node-scoped gate)

With explicit edges, a new mode audits **Cone(X) ∪ transitive-closure(declared deps)** bottom-up, reusing
the existing order-parametric engine (`_audit` / `_audit_with_manifest` already take an arbitrary
`[(name,[occs])…]`). Passing it ⟹ X's slice of the final build is green end-to-end — the honest answer to
"is step7 *genuinely* done," which `--subtree` cannot give for a leaf-with-hypotheses. It is still NOT a
whole-prop gate (the final Main combine + global no-stray-sorry remain `--all`'s job).

## Part C — contract-hash incremental certificates ("certify once, never go back")

This largely *exists* as the `--whatchanged` manifest, which today keys a node's certificate on its own
input FILES (backing file + containers it's wired in). That's sound but **coarse**: any edit to a shared
container (e.g. `Main.lean`) invalidates *every* node wired there. Explicit deps let us tighten it from
file-granular to **contract-granular**:

```
cert(X) = hash( X.lean , X's claim-in-container , { CLAIM-hash of each declared dep } )
```

The decisive choice is **claim-hash of each dep, not file-hash**:

- A dep's **proof** changes (you refactor `step7_dfpar_boffDG`) → its claim is unchanged → **X's cert
  still holds; you never re-audit X.** You only re-verify the dep itself.
- A dep's **claim (contract)** changes → X's cert breaks → re-audit X and *only* its dependents (the exact
  reverse-edge set, cheaply computed from the explicit graph).

So invalidation tracks *contract* churn (rare), not *proof* churn (constant). This is a build cache /
Merkle DAG with the dependency key chosen as the contract.

## Part D — it's recursive (every `have`, not just sentences)

A `have` is structurally a node like a sentence (named claim + backing file + canonical wire), so `@deps`
+ contract-cert apply **uniformly and recursively** — consistent with the pipeline already being "one
recursive atom." Two recursion-specific points:

- **An inner `have`'s deps have two source kinds:** (1) earlier **sibling `have`s** in the same container
  (node→node edges, like sentences) and (2) the **container's own signature binders** (the objects/hyps
  the container was *given* — an edge to the container's *interface*, keyed on the container's signature,
  which moves only on a re-spec).
- **Recursion is what bounds the blast radius.** Because every node exposes only its **contract (claim)**
  upward, a proof change bubbles up exactly as far as the nearest unchanged contract — almost always zero
  levels. Tweak one have inside `step7_dfpar` → re-verify that have (+ its dependents/combine *inside*
  `step7_dfpar`) → `step7_dfpar`'s claim is unchanged → `step7` and everything above never re-run. Without
  recursing the inner haves, the same edit coarsely re-runs all of `step7_dfpar`.

## Part E — `--context` provenance (diagnostic, keep it cheap)

To help the agent decide what to name, `--context` should classify each context hyp by type-matching it
against (node claims | construction outputs | premises) and label it "supplied by step7_dfpar" /
"premise" / "unknown". Put the *fragile* type-matcher HERE, where a miss costs nothing — it's only advice.
The same matcher used as a *gate* would be unsound (see open questions).

## Why it helps (cost terms)

Builds are free; the expense is agent cognition. This idea attacks two sources:

- **#3 (test + pinpoint):** a deterministic named-discharge failure points at the exact missing/wrong
  producer instead of a vague "could not prove." `--node-complete` gives a true done/not-done for a node
  without the agent reasoning about whether siblings are covered.
- **#4 (meta — am I off-track / did I break something?):** after an edit, contract-hash invalidation
  reports the **precise minimal re-check set** ("step7_dfpar's contract changed → re-audit {step7}; nothing
  else"), so the agent never re-reasons about untouched, still-certified work. "Certify once, never go
  back" is the cognition saver, not the build-time saver.

## Open questions / risks

- **The guarantee is exactly as complete as the explicit-dep graph.** Every remaining `(by assumption)`
  hyp is an *untracked edge*; for those you must fall back to conservative container-level invalidation, or
  the diagnostic matcher (unsound as a gate). The no-cascade promise strengthens monotonically with naming
  discipline — a fully-named node gets the full guarantee, a partially-named one only up to its named hyps.
- **Hash the NORMALIZED claim, not raw bytes** — reformatting or α-renaming a claim must not invalidate
  dependents. Parse → normalize → hash. (Defeq-but-syntactically-different still invalidates: the safe
  direction.)
- **Shared haves have a contract PER call site.** A reused helper gets different providers per parent, so
  its `@deps` and its cert are **per-occurrence** (a conjunction over sites). The manifest currently keys
  certs by *name* → needs per-(name, site) certs, or a conservative "invalidate if any site changed." This
  is the one place bookkeeping genuinely gets harder.
- **The combine is a consumer at EVERY level**, not just Main's final `exact` — each container's tail
  depends on its sub-haves' claims and must re-check on a sub-claim change.
- **`exact name` matches up to defeq, same strength as `assumption`** — no new false-negatives from
  matching *strength*, only from *candidate restriction*: a producer in a different orientation than the
  binder wants will fail where loose `assumption` found a reoriented copy. Arguably correct (forces stating
  the true dependency) but adds friction.
- **Surface-area cost.** Changing the wired-body shape touches `wired_body`, `_body_regexes` (the matcher
  that keeps false positives "structurally impossible" — widen carefully), `set_node_isolated_sp`,
  `wire_main`, and `integrity_scan`. **De-risk first:** prototype the hybrid wire on `step7` alone —
  convert its `(by assumption)`s to named producers, confirm `euclid_apply` accepts a bare identifier in
  hyp position and SP still passes — before touching any generator/matcher code.
- **Uniform mechanism ≠ obligation to annotate every have.** The incremental machinery earns its keep at
  *expensive* re-audit boundaries (sentences, big containers); for a ≤30s leaf container, just rebuild it.
  Make it available everywhere; spend naming effort where re-audit is costly.

## Relationship to other ideas

- Builds directly on the existing **`--whatchanged` manifest** (this is its contract-granular successor).
- Complements **06 context-slimmer**: slimming drops unused hyps → fewer edges to declare → smaller,
  cleaner dep graph. Do 06's "which hyps were used" first and the `@deps` list is mostly written for you.
- Orthogonal to **01 fact DB** (that's about *finding* lemmas; this is about *recording* what a proof
  consumed once found).

## Staged build order (de-risk before committing surface area)

1. **Spike:** hand-convert `step7`'s `(by assumption)`s to named producers; confirm `euclid_apply` accepts
   it + SP passes. (Answers the format-feasibility risk.)
2. **`@deps` / pass-by-name in `wired_body`** + widen `_body_regexes`; keep `(by assumption)` as the
   fallback token (hybrid). Update `integrity_scan` to recognize both.
3. **`--node-complete X`** mode over Cone(X) ∪ closure(deps) (reuses `_audit_with_manifest`).
4. **Contract-hash certs:** change the manifest's dependency dimension from file-hash to dep-claim-hash;
   `--whatchanged` then reports the proof-churn-immune minimal recheck set.
5. **`--context` provenance labels** (diagnostic matcher).
6. Recurse to inner `have`s + the per-occurrence cert for shared haves (the hardest bookkeeping; do last).
