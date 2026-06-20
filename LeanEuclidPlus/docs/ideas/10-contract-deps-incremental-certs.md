# 10 — Explicit named dependencies + contract-hash incremental certificates

**Status:** idea (actively developing) · **Serves:** #3, #4 (+ #1/#5 clarity) · **Effort:** med-high
(staged) · **Priority:** **Program 3 (cleanup/maintenance) — NOT a priority for finishing Book 2.** This
pays off when proofs are *done and churning* (certify-once, invalidation, readability), not in the
get-it-green regime. Record richly; spike the named-wire on ONE node before committing surface area.

> **How `@deps` gets computed — the operator's-question resolution (recorded, don't relitigate).**
> "`@deps` doesn't exist yet — for each node, how does a SCRIPT figure out the minimal deps?" Resolved:
> there is **no combinatorial search** (no n! over hyp subsets). The named-node set is *parsed* from Main
> (`parse_occurrences`), never searched. Two sound mechanisms, both polynomial:
> - **Leave-one-out (cheap, ~context-size builds):** with all facts in context the wire is green; remove
>   ONE context fact, rebuild once (that one build re-checks all the helper's slots at once), fails ⟹ that
>   fact was necessary ⟹ a dependency. O(context) builds per node, not slots×context.
> - **Per-slot `exact` (sound under redundancy, ~slots×candidates builds):** for each helper slot, try each
>   same-type context fact via `exact`; Lean accepting it IS the check (not a fragile matcher). Type-filter
>   by head symbol FIRST to skip non-matching facts (a `formParallelogram` slot only tests the 2–3
>   `formParallelogram` facts) → ~tens of builds/node, not thousands.
>
> **The redundancy hole and its fix (operator's call):** if TWO context facts can discharge the same slot,
> leave-one-out breaks SILENTLY (remove either, the other still covers it ⟹ both reported "unused" ⟹
> under-declaration, the boffDG bug class). Per-slot `exact` instead SEES both and flags ambiguity. BUT —
> "two facts concluding the same thing" is **redundant by definition** (they're defeq at the wire, else
> only one would `exact`-match), which is **bad proof design the agent should remove**, not engineer
> around. So the chosen path is: **lint out same-conclusion redundant facts**, after which **leave-one-out
> is sound and minimal** — cheapest, no slot-search, no core change. Mis-attributing between two genuinely
> defeq producers is HARMLESS anyway (you can only ever trigger a *spurious* future re-audit, never SKIP a
> needed one: if a recorded producer's contract later changes it's no longer defeq, so it stops discharging
> the slot and the build catches it — the safe direction). Cost is per-node, computed ONCE, then cached by
> the contract-hash cert and never recomputed until that node or a dep's *contract* changes.

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

### The hybrid is forced — and "name everything" is the WRONG fix

Most of a helper's hypothesis binders are NOT named nodes. Empirically (Prop05/Main.lean, `step7`'s wire):
~6 of `step7`'s ~20 binders are named node-outputs (`hcmpar, hdfpar, hlhm, hdhg, hbmf, hstep6`); the other
~14 are **unnamed interface facts** — incidence/betweenness/non-intersection from the proposition premises
(`euclid_intros`, line 15) and from constructions (`proposition_46 … as (e,f,EF,CE,BF)` names the 5 OBJECTS
but dumps its ~7 geometric facts into context anonymously). So you **cannot** make every hyp arg a name —
`(by assumption)` exists precisely because these facts are anonymous.

And **naming them all would be actively wrong.** Facts are unnamed because the consuming tactic is
name-blind: `euclid_finish`/`euclid_apply` translate the *whole local context* to SMT and discharge by
solving — they reference facts by translated value, not by name. Naming buys zero proving power, and many
facts (`between l h m`, parallel/non-intersection) are never separate hyps at all — the solver infers them.
To name them you'd hand-write a `have`+proof per inferred fact, which is exactly the plumbing the SMT
backend exists to eliminate. Naming-all fights the grain of System E and bloats every proof. **Rejected.**

So each hyp arg is **either a declared producer-name or `(by assumption)`** (hybrid). This matches the
"lazy → list all → only `--all`" intuition at per-hypothesis granularity.

### The soundness hole, and why discharge MUST be restricted

A free `(by assumption)` re-opens the exact false-confidence bug at the cert level: the AI omits a `@deps`
entry, but the producer fact is sitting in the parent context (a named sibling `have`), so `(by assumption)`
finds it anyway → the node-scoped check **passes** while the producer was never audited → the certificate is
a lie (and invalidation won't fire when that producer's contract later changes). So: **discharge must be
restricted to (declared deps ∪ stable interface); a binder that secretly needs an *undeclared* sibling must
FAIL.**

Lean has **no `assumption only [hyps]`** (core `assumption` always scans the full context; `solve_by_elim`'s
hyp control is too coarse). But the restriction is achievable with a built-in, because the *disallowed* set
is exactly the **named node-outputs**, which the script enumerates (`parse_occurrences`). The script-generated
wire becomes:

```
clear <every node-have EXCEPT the declared deps> ; <exact the declared deps ; (by assumption) for the rest>
```

After the `clear`, `(by assumption)` can only see {declared deps} ∪ {unnamed interface}. A binder secretly
needing an undeclared sibling is now unreachable → fails loud → forces the declaration. The AI can't dodge
it: **only the script writes wiring**, so the `clear` is always emitted. `clear` is safe here — node-haves
are Prop-typed, nothing references their proof terms (proof irrelevance), so the clear can't be blocked by a
context dependency. A ~15-line `discharge_from [decls]` tactic can wrap clear+exact+assumption for tidiness,
but it is **not** required for soundness — `clear … ; assumption` already is.

### Why this is sound — verified against the SystemE source (not assumed)

The whole scheme rests on one property: **no node's fact appears ANONYMOUSLY in a consumer's parent context**
(else clearing the named node wouldn't remove the anonymous copy). This is *guaranteed* by how
`euclid_apply` works ([SystemE/Meta/Tactics/Solve.lean](../../SystemE/Meta/Tactics/Solve.lean)), confirmed by
reading it:

- **`(by assumption)` is core Lean `assumption`** — it matches a hyp whose type is *defeq* to the binder.
  `A ∧ B` is not defeq `A`, so it **does NOT project a conjunct**: a binder `: A` is not satisfied by
  `step1 : A ∧ B ∧ …`. (This kills the "conjunction" worry — it's the safe direction.)
- **A wired sentence does not leak destructed atoms.** `elimAllConjunctions` (Solve.lean:197) and
  `aesop_destruct_products` (Solve.lean:70) split *only the conclusion just obtained by that `euclid_apply`*,
  in the *current* tactic state. For `have stepN : C := by euclid_apply (…); …`, that splitting happens
  INSIDE the have's proof; at the `have` boundary only `stepN : C` (whole, named) escapes to Main.
- **Constructions DO destruct — into the interface.** `euclid_apply (…) as (…)` runs at Main level, so its
  conclusion is split into atomic anonymous hyps in Main. Those are the (tracked) premise/construction
  interface, a function of the construction lemma + objects — never of a node claim.

Consequence: in Main, a node's conjunct exists *only* inside the whole named `stepN`; `assumption` can't pull
it out; there is no anonymous atomic copy to sneak past a clear. So clearing the named node (if undeclared)
genuinely makes its facts unreachable → under-declaration fails loud. **Sound, by construction of the wire +
the have boundary — not modulo an open invariant.** (The only persisting Main-level tactics are constructions
— facts = f(lemma, objects) — and the top-level `euclid_intros`; `euclid_finish`/`solveWithProvers` close
goals without persisting hyps. So no tactic ever materializes a persistent node-derived anonymous fact.)

## Part B — `--node-complete X` (sound node-scoped gate)

With explicit edges, a new mode audits **Cone(X) ∪ transitive-closure(declared deps)** bottom-up, reusing
the existing order-parametric engine (`_audit` / `_audit_with_manifest` already take an arbitrary
`[(name,[occs])…]`). Passing it ⟹ X's slice of the final build is green end-to-end — the honest answer to
"is step7 *genuinely* done," which `--subtree` cannot give for a leaf-with-hypotheses. It is still NOT a
whole-prop gate (the final Main combine + global no-stray-sorry remain `--all`'s job).

Crucially it **cache-hits on already-certified deps**: a dep X whose cert is still valid is *not* re-walked
— Y only checks X's contract (its binder discharges) and that X's cert is fresh. So certifying Y is local
(Y's own cone + dep-contract/freshness checks), and a dep shared by many users is audited once, not per
user. That's the dependency-cert payoff: "X's subtree is already done; don't redo it for every Y."

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

## Part F — ALTERNATIVE substrate: auto-named interface facts (System-E change) — NOT a priority

A different way to get explicit deps: instead of the script *recovering* dependency edges by build-search
(leave-one-out / per-slot `exact`), change **System E itself** so the anonymous facts are NAMED at the
source — then the wire reads its deps off names, no recovery needed.

**What's anonymous today, and what naming targets.** The helper's slots are ALREADY named (its signature).
The only anonymous fillers are the **construction outputs**: `euclid_apply (proposition_46 …) as (e,f,EF,…)`
names the 5 OBJECTS but dumps its ~7 geometric facts into Main's context unnamed (premises are already
bound by the proposition signature; solver-*inferred* facts like `between`/parallel are never hyps at all,
so they're neither nameable nor needed). So this change is narrow: **auto-name the construction-output
facts** (extend the `… as` handling in `Solve.lean` / the construction tactics to introduce hygienic
names), via a stable convention derived from the producing lemma's conclusion structure (e.g. `prop46.fpar`,
NOT positional `prop46.3` — positional shifts if the lemma's conjuncts reorder).

**Why it's safe and the operator's objections were answered:**
- **Cannot break anything** — naming is *additive*. `euclid_finish` translates the whole context regardless
  of names; `(by assumption)` is name-blind; every existing proof builds identically. Old `(by assumption)`
  wires keep working — incrementally adoptable, no migration.
- **Brittleness defused** — the earlier "positional names go stale on reorder" objection only bites if
  names are HAND-maintained. Here **the script regenerates the wiring** whenever a producer changes, so
  names are always freshly correct; staleness is impossible.

**What it actually buys (provenance, not proving power — naming gives `euclid_finish` ZERO new power):**
- **Deps become parse-readable** — "what does step7 depend on" = read the named wire; zero builds ever to
  *recall* deps (vs. `(by assumption)` recording nothing).
- **Stable producer-tie for invalidation** — exactly what Part C's contract-certs need.
- **Drops the load-bearing no-anonymous-leak property** (Part A) — nothing is anonymous anymore, so the
  `clear`-soundness argument isn't needed.

**Why it's NOT a priority (operator's call):** it's a change to the **trusted tactic core** everything
depends on, for a **bookkeeping/readability** payoff that lands in the certify-once/maintenance regime —
not in the get-it-green regime of finishing Book 2. The zero-core-change path (lint redundant facts +
leave-one-out, in the box at the top) gets sound deps TODAY. **Auto-naming is the better PERMANENT
substrate to migrate to once the corpus stabilizes — recorded as a good readability/cleanliness idea,
explicitly deferred.**

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

- **Soundness depends on the `clear`, not on naming discipline.** With clear-scoping, the `(by assumption)`
  remainder can only resolve against the stable interface (premises/constructions, tracked as container
  source) — *not* against an undeclared sibling (those are cleared, so a missing dep fails loud). So
  under-declaration is a build failure, not a silent pass: a node need NOT name every hyp to be sound, only
  its sibling-node edges. (The interface remainder is tracked coarsely — at container-source granularity —
  which is correct, since those facts are a function of Main's source, never of a node claim.) This is why
  the scheme is sound even for a "lazy" node that names only some hyps: the clear handles the rest.
- **The soundness rests on a verified property of the wire, not an open invariant** (see Part A): core
  `assumption` doesn't project conjuncts, and a wired sentence leaks only its named claim past the `have`
  boundary. If the wired-body shape ever changes (e.g. dropping the `have` wrapper, or a tactic that
  *persists* context-saturated hyps mid-Main-body is introduced), re-confirm this — it's the load-bearing
  fact.
- **Hash the NORMALIZED claim, not raw bytes** — reformatting or α-renaming a claim must not invalidate
  dependents. Parse → normalize → hash. (Defeq-but-syntactically-different still invalidates: the safe
  direction.)
- **Shared haves are dependency fan-in — NOT a per-occurrence cert.** Certification is per-node and once:
  X's subtree is established by X's own `--subtree`/cert. When a user Y is full-certed and uses X via
  `@deps`, Y references X's **contract** (its binder discharges against X) and **cache-hits** on X's cert —
  it does NOT re-audit X's cone. So X used by Y1 and Y2 is plain fan-in: one cert for X, each user
  references it. "Does Y1 supply X's hyps" lives in *Y1's* cert, "does Y2" in *Y2's* — those certs already
  exist independently; X carries neither. The only cross-node mechanism is the **reverse edge**: X's
  *contract* changes → invalidate its dependents {Y1, Y2}; X's *proof* changes → contract unchanged →
  dependents untouched. (Standard build-cache resolution; no per-(name,site) cert.) The one real mechanical
  requirement: `--node-complete Y` must **skip an already-certified dep's cone** (cache hit) rather than
  re-walk it, and the manifest must carry the reverse edges — that's the feature, not a hard problem.
- **The combine is a consumer at EVERY level**, not just Main's final `exact` — each container's tail
  depends on its sub-haves' claims and must re-check on a sub-claim change.
- **`exact name` matches up to defeq, same strength as `assumption`** — no new false-negatives from
  matching *strength*, only from *candidate restriction*: a producer in a different orientation than the
  binder wants will fail where loose `assumption` found a reoriented copy. Arguably correct (forces stating
  the true dependency) but adds friction.
- **Surface-area cost.** Changing the wired-body shape (named args + the `clear` prefix) touches
  `wired_body`, `_body_regexes` (the matcher that keeps false positives "structurally impossible" — widen
  carefully), `set_node_isolated_sp`, `wire_main`, and `integrity_scan`. **De-risk first:** prototype the
  hybrid wire on `step7` alone — convert its sibling-node `(by assumption)`s to named producers, add the
  `clear <other nodes>` prefix, confirm `euclid_apply` accepts a bare identifier in hyp position and SP
  still passes — before touching any generator/matcher code.
- **Perf of the `clear`.** Negligible — `clear` is local-context fvar removal (~10–15 per wire), and the
  discharge is zero-SMT `assumption`; a smaller context makes both `assumption` and euclid_apply's citation
  translation marginally *faster*, never slower. The expensive path (SMT) is never on the wire.
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

1. **Spike:** hand-convert `step7`'s sibling-node `(by assumption)`s to named producers + add the
   `clear <other nodes>` prefix; confirm `euclid_apply` accepts a bare identifier in hyp position, the
   clear doesn't break the discharge, and SP still passes. (Answers the format-feasibility risk.)
2. **`@deps` + clear-scoping in `wired_body`** (named args for sibling-node deps, `clear` of all other
   node-haves, `(by assumption)` fallback for interface hyps) + widen `_body_regexes`; update
   `integrity_scan` to recognize the new shape.
3. **`--node-complete X`** mode over Cone(X) ∪ closure(deps), reusing `_audit_with_manifest`. Make it
   **cache-hit on already-certified deps**: don't re-walk a dep's cone if the dep's cert is still valid —
   just check its contract. (This is the "X's subtree is already done" optimization; shared deps fall out
   of it for free.)
4. **Contract-hash certs + reverse edges:** change the manifest's dependency dimension from file-hash to
   dep-claim-hash, and record dependents; `--whatchanged` then reports the proof-churn-immune minimal
   recheck set (a dep's *contract* change invalidates its dependents; a *proof* change doesn't).
5. **`--context` provenance labels** (diagnostic matcher).
6. Recurse to inner `have`s (uniform mechanism; spend naming effort only at expensive boundaries).
