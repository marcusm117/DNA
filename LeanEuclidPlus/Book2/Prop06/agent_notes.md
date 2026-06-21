# Prop06 — agent notes

## 2026-06-20 (resume): BLOCKED by a pipeline tooling regression (smell shape ⇒ false "node")

**Symptom.** `check_step Book2/Prop06 --check` reports 25 "node 'X' has NO backing file 'X.lean'"
for X ∈ {hac, hak, hkm, hbd, hcbd, hcd, hcene, hde, hbase, hbc, hhg, hhl, hlc, hle, hhe, hbnsg,
hdc, hfe, hke, hacd, hace, hcnse, hensf, hlnsm, hlsse_bg}. `--status` shows steps
1,2,3,5,6,7,8,9,10,11,13,15 as todo (cones "have uncertified node(s)") even though my memory had
steps 1–6 certified.

**Root cause (NOT a Prop06 defect).** Every flagged X is a *legitimate inline single-line proof*
`have X : T := by euclid_finish` inside a container (e.g. step11.lean:57-59, step11_bdbh.lean:31-39),
sitting next to multiline inline proofs (hABKM, hcoffDE, hray2) that are NOT flagged. These predate
smell-mode (committed at 66c1d97 / 6c38da6, before 9b2710c "added smell mode").
Commit 9b2710c added a 4th canonical body shape "smell" = `:= by euclid_finish` to
`faithful_lib._body_regexes`. `parse_nodes_in_file` (faithful_lib.py:767-771) now appends ANY
smell-shaped `have` as a *node*, so `parse_occurrences`/`integrity_scan`/`audit_order`/`cone_names`
treat each legit inline `euclid_finish` proof as a node-needing-a-backing-file. The `--smell` doc
itself says this shape is "transient, never written to disk persistently" — so a persisted bare
`euclid_finish` should be read as a finished inline proof, exactly as the pipeline did pre-9b2710c.

**Scope = whole book, not Prop06.** `check_step Book2/Prop05 --check` shows the SAME false nodes
(h1, h2, hac, hbd, …) even though Prop05 is the confirmed-done, Phase-C-wired, `check_faithful.sh`-
passing prop (commit 3917ce2). The real Lean builds + faithfulness checks are fine; only the
source-regex node-discovery is wrong. This blocks `--subtree`/`--all` on every cone that contains
such a `have` (SP would call `backing_file(X)=None` → FaithfulError), so proving cannot resume until
node-discovery is fixed.

**Recommended fix (one line, low risk).** In `faithful_lib.parse_nodes_in_file`, skip smell-state
haves in persistent discovery:
```python
        state, bs, be = body
        if state == "smell":
            continue            # a finished inline `euclid_finish` proof, not a pipeline hole
```
The transient `--smell <node>` flow is unaffected: it identifies its target by the node's `:= by
sorry` body, swaps to smell, builds, and reverts via `restore_files`' byte snapshot — it never
needs to *discover* a persisted smell node. Awaiting human go-ahead before touching verification
tooling.

## 2026-06-20 (resume cont.): tooling fix applied + progress + step9 fix

Tooling fix APPLIED (human-approved): `parse_nodes_in_file` now skips `state=="smell"`. --check green.
Certified in order this session: step1,2,3,5,6,7,8 (step7 = 37-node cone). Already-done: 4,11,12,14,16.
13/16 Main nodes green. Remaining: step9 (in progress), step10, step13, step15.

**TO DELETE (human, safe):** `Book2/Prop06/step9_doffkm.lean` — UNTRACKED scratch file from this
session (a dead-end attempt to prove `d∉KM` locally). Superseded; see below. Keep STATUS.md + this file.

**step9 gap = missing witness.** step9's cone needs `d∉KM`. step9.lean called the shared `step7_doffkm`,
which needs a witness point `h ∈ KM` off AB (step7 & certified step11 carry `h`; step9 didn't). `d∉KM` is
NOT provable from step9's local facts — the parallel-line distinctness `KM≠AB` is circular without `h`
(KM = proposition_31 h a b AB, Main:37; the non-degeneracy lives in h/BG/DE). `--context step9` confirms
Main supplies `h, BG, DE` + `h.onLine KM/DE/BG`, `b.onLine BG`, `d.onLine DE`, `e.onLine DE`,
`¬BG.intersectsLine CE`. FIX: thread `h, BG, DE` + those 7 facts into `helper_2_6_step9`'s signature, and
in the body reuse two ALREADY-CERTIFIED helpers as nodes — `step6_hoffab` (`¬h.onLine AB`) then
`step7_doffkm` with `-- @args: d h AB KM`. No new backing file. step9_ampar takes `d∉KM` by type, so the
node name (step7_doffkm vs step9_doffkm) is irrelevant to it.

**step10:** body was `linarith` (not in scope under `import SystemE`) + missing `namespace
Elements.Book2`. Rewrote with namespace + `euclid_finish` (pure area-arith, mirrors step12).

**step15_sqpar / step15_sqpar_a** (square CEFD as formParallelogram): `all_goals first | assumption |
euclid_finish` couldn't close a `distinctPointsOnLine` `≠` conjunct (`d≠f`, `e≠f`) — the same
parallel-distinctness gap as step9. Added one off-line witness hyp to each sig (`¬(d.onLine EF)` ⟹ d≠f;
`¬(e.onLine DF)` ⟹ e≠f), both Main-suppliable. euclid_finish then closes.

## 2026-06-20 — PHASE B COMPLETE. Handing to human for Phase C.
`check_step Book2/Prop06 --status` → 16/16 Main cones ✓, 3/3 whole-prop checks ✓ ⟹ `--all` guaranteed.
Files changed this session: scripts/faithful_lib.py (smell-skip tooling fix), Book2/Prop06/{step9,
step10,step15_sqpar,step15_sqpar_a}.lean. No claim types touched (only helper sigs + bodies).
HUMAN NEXT:
  1. rm LeanEuclidPlus/Book2/Prop06/step9_doffkm.lean   (untracked dead-end scratch)
  2. python3 scripts/check_step.py Book2/Prop06 --all     (final witness, 2.5-7 hr; guaranteed 0)
  3. python3 scripts/wire_main.py Book2/Prop06  +  scripts/check_faithful.sh Book2  +  check_steps.py
     +  check_signatures.py   (Phase C)
