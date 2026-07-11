# Prop20 (III.20) — central angle = 2 × inscribed angle (same base BC)

## ✅✅ PHASE B COMPLETE — 13/13 Main nodes certified, 3/3 whole-prop checks green.
`--status` all-green ⟹ `--all` guaranteed. Ready for Phase C (human: wire_main.py + check_faithful.sh).
Two Phase-A fixes made (our unfaithfulness): f & g constructions (extend_point → intersection_circle_line_
extending_points), and hd_ex strengthened to `d.sameSide e BC` (+ parallel-diameter existence construction).
Diameter degeneracies handled as @euclid_gap case-splits (step2/4/6 chord-diameter; step7/step12 f∈{b,c}).
Dead files (safe to delete): hcb_AEF.lean, hsec.lean (early case-2 experiments, made trivial), and
step7_subE.lean / step7_subA.lean (unused trivial sum_angles leaves — step7_case2 inlines sum_angles now).
step7_case2.lean itself is LIVE.


Figure: circle ABC, centre e. Base chord BC (b,c on circle & on BC). Inscribed vertex a with
`a.sameSide e BC`. Antipode f of a (diameter A-E-F). Second vertex d + antipode g.
Goal: `∠ b:e:c = ∠ b:a:c + ∠ b:a:c` (closed by `exact step7`). Steps 8-12 = Euclid's second
configuration for d (extra faithfulness sentences; do NOT feed the goal).

## CERTIFIED (Phase B)
- **Construction fix (our unfaithfulness, done):** `f` was `extend_point` (⟹ `f.onCircle` NOT entailed).
  Now `intersection_circle_line_extending_points ABC AEF e a` (true "produce AE to F on circle").
  **DO THE SAME for `g` in step9** (currently `extend_point DEG d e` → `intersection_circle_line_extending_points ABC DEG e d`).
- **step1..step6 CERTIFIED.** step2 (isoceles EAB, prop_5), step4 (ext-angle prop_32), step6 =
  step6_isoc (prop_5) + step6_ext (prop_32), each with a `-- @euclid_gap` diameter case-split
  (`by_cases X.onLine AEF`; when chord AB/AC is a diameter the sub-triangle degenerates, closed by euclid_finish).
  step3/step5 = angle arithmetic.

## step7 — DONE ✅ (the crux, fully certified — 9 sub-nodes).
Structure: `by_cases hfs : f.sameSide a BC`.
- Case 1 (¬hfs): `by_cases hfBC : f.onLine BC`. Degenerate (f=b/f=c, AB/AC diameter) → `step7_c1deg`
  (= `step7_c1deg_fbc` proving f=b∨f=c via `between_points`+`circle_points_between` contradiction, then
  `step7_c1deg_fb`/`_fc` using `equal_angles` for the ray-coincidence ∠EAC=∠BAC). Non-degenerate → hopp +
  `step7_addA`/`step7_addE` (crossing x=AEF∩BC, sum_angles).
- Case 2 (hfs): `step7_case2` = `step7_case2_hsec` (crossing gives c.sameSide b AEF; euclid_finish then
  supplies the sector sameSide facts as a disjunction) + inline sum_angles (rcases 2a/2b, subtraction).
KEY TOOLING FIX: sub-node files MUST be prefixed with a Main-node name (`step7_...`) or the order/edit
hook rejects them ("does not match any Main-level node"). That (not nesting depth) was the earlier block.

## (historical) step7 crux notes
III.20 needs TWO configs (Euclid uses two points; the formal `a` is GENERIC so BOTH occur):
Case 1 = E inside ∠BAC (diameter AF SEPARATES b,c) → ADDITION; Case 2 = E outside → SUBTRACTION.
Counterexample proving case 2 is admissible (all hyps hold): unit circle, e=(0,0), a=(1,0), f=(-1,0),
b=(-0.8,-0.6), c=(0.8,-0.6): a.sameSide e BC ✓, but E outside ∠BAC; ∠bef+∠fec=180°≠∠bec=106.26°.

`step7.lean` = `by_cases hfs : f.sameSide a BC`:
- **Case 1 (¬hfs): DONE.** `have hopp : a.opposingSides f BC := by euclid_finish` then leaves
  **step7_addA** (∠bac=∠bae+∠eac) + **step7_addE** (∠bec=∠bef+∠fec), both PROVEN (`--provable` green).
  Recipe (each leaf, takes hopp): crossing x = AEF∩BC via `intersection_lines_opposing` →
  `intersection_lines` → `pasch_4` (between a x f) → `circle_points_between` (x inside) →
  `circle_line_intersections` (between b x c) → euclid_finish (between e x f / a e x) →
  `line_from_points` EB/EC (or AB/AC) → `pasch_2`×2 (sameSide) → `sum_angles_onlyif` → euclid_finish.
- **Case 2 (hfs): STUB `step7_case2` (needs proving).** RECIPE below. The two trivial sum_angles
  leaves already exist & BUILD (reuse them): **step7_subE** (∠fec=∠feb+∠bec) and **step7_subA**
  (∠eac=∠eab+∠bac) — each takes the two `sum_angles_onlyif` sameSide facts as HYPS and just applies
  it. They're generic; the 2b orientation reuses them with b,c swapped via `-- @args: a c b e f AEF EB` etc.

### Case-2 recipe (for step7_case2.lean)
The hard part = supplying the sum_angles sameSide facts. `euclid_finish` CANNOT derive them (times out).
Key derivable fact: **c.sameSide b AEF** (b,c same side of the diameter AEF). Proof: `by_cases AEF.intersectsLine BC`;
in the crossing branch get x=AEF∩BC; since a,f SAME side of BC (case 2) ⟹ ¬between a x f ⟹ x outside the
chord AF ⟹ `x.outsideCircle` ⟹ ¬between b x c ⟹ c.sameSide b AEF; parallel branch is trivial.
Then a **same_side_pigeon_hole** (cf. Book3/Prop16, Book1/Prop07) decides whether B or C is inside sector
FEC, giving the remaining facts (f.sameSide b EC & e.sameSide b AC for 2a; the c-analogs for 2b).
STRUCTURE to dodge the tooling limit (see below): make the WHOLE sameSide bundle ONE top-level sub-node
disjunction in step7_case2.lean, e.g.
`have hsec : (f.sameSide b EC ∧ e.sameSide b AC ∧ c.sameSide b AEF) ∨ (f.sameSide c EB ∧ e.sameSide c AB ∧ b.sameSide c AEF) := by sorry`
(offload its crossing/pigeon-hole proof to hsec.lean), then `rcases hsec` and call step7_subE/subA per branch,
`euclid_finish` combines (∠bec = ∠fec−∠feb = 2∠eac−2∠eab = 2∠bac).

⚠ **TOOLING LIMIT hit:** a pipeline sub-node (backing file) nested TWO `by_cases`/`rcases` deep in a
container was NOT recognized by the Edit/order hook ("does not match any Main-level node"). Keep sub-nodes
at ONE branch-level, or push deeper case-work INTO a leaf's own body (internal by_cases are fine — they
make no pipeline nodes). Dead files left behind: `hcb_AEF.lean` (orphan stub, ignore/remove).

## hd_ex — DONE ✅. step8 — DONE ✅. g-construction FIXED (Main).
hd_ex proven via the parallel-diameter construction (Book1.proposition_31 + intersection_circle_line_2 +
intersections_circle_line). step8 trivial (repackages the obtain). g construction in Main fixed
extend_point → intersection_circle_line_extending_points (same as f).

## D-branch (step9-12) REMAINING — reuse via @args (NO new hard leaves needed):
- step9: like step1 (distinctPointsOnLine d e DEG ∧ g.onCircle ∧ between d e g) from the fixed g construction.
- step10 (∠gec=2∠edc): container REUSING helper_3_20_step6_isoc + step6_ext via `-- @args: d c e DEG ABC …`
  (step6 is generic in a,c,e,AEF). step11 (∠geb=2∠edb): same with c→b.
- step12 (∠bec=2∠bdc): container mirroring step7.lean, REUSING step7_addA/addE/case2/c1deg via @args
  (d b c e g DEG …). The full step7 cone re-instantiated for the d/g config. Largest, but pure reuse.

## hd_ex — (historical) construction notes
Map under-constrained d (⟹ step12 false for minor-arc d). FIXED in Main: `hd_ex` now
`∃ d, d.onCircle ABC ∧ b≠d ∧ c≠d ∧ a≠d ∧ d.sameSide e BC` (+ obtain updated). `d.sameSide e BC` ⟹ d off BC
⟹ d≠b,c FREE, so only d≠a needs care. CONSTRUCTION (drop into hd_ex.lean, imports Book1.Prop31.Main):
```
have he_off_BC : ¬ e.onLine BC := by euclid_finish
euclid_apply (Elements.Book1.proposition_31 e b c BC) as Q      -- Q ∥ BC through centre e
euclid_apply (intersection_circle_line_2 e ABC Q)               -- Q meets circle (e inside, on Q)
euclid_apply (intersections_circle_line ABC Q) as (q1, q2)      -- both on e's side (Q∥BC)
by_cases hq1a : q1 = a
· exact ⟨q2, by euclid_finish, …×5⟩       -- q2≠a since q2≠q1=a
· exact ⟨q1, by euclid_finish, …×5⟩
```
So NO real blocker: a second major-arc vertex IS constructible (parallel-diameter trick).

## D-branch (step8-12) — mostly REUSE, once step7 is generic.
- step8: trivial (restate d props from the obtain).
- step9: fix g construction (extend_point→intersection_circle_line, as f) + props like step1.
- **step10 (∠gec=2∠edc) = helper_3_20_step6 applied with (d,c,e,g,DEG,ABC)** — REUSE (step6 is generic).
- **step11 (∠geb=2∠edb) = helper_3_20_step6 (d,b,e,g,DEG,ABC)** — REUSE.
- step12 (∠bec=2∠bdc) = the step7 machinery for the d/g config (subtraction). Reuse step7's leaves generically.
No new hard reasoning beyond step7; the d-branch is the SAME crux re-instantiated.
