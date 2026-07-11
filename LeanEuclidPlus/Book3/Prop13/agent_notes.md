# Prop13 (III.13) — PHASE B COMPLETE (19/19 nodes ✓, 3/3 whole-prop checks ✓)

Final `--all` witness run after `--status` reported "GUARANTEED to pass". Awaits human Phase C
(`wire_main.py`) + gate-C (`check_faithful.sh` + `check_steps.py` + `check_signatures.py`).

## Dependency note — needs human at gate C
Prop13 cites III.11, whose SIGNATURE was corrected during this work (added `|(g─a)| < |(f─a)|`, the
inner-circle radius condition — III.11 was FALSE as originally stated; see Book3/Prop11/agent_notes.md).
So `check_signatures.py --save` + `check_steps.py --save` for BOTH Prop11 and Prop13 are pending (human).
step16 cites [Def.~3.3] (a Definition, not a `proposition_*`), so criterion-3 (prop-number only) passes.

## The crux: step4 + the "two common points ⟹ circles intersect" construction (`step4_int`)
The III.11 fix means step4's `euclid_apply (proposition_11 …)` needs the radius precondition
`|(h─d)| < |(g─d)|` (EBFD is the inner circle). In Prop13's reductio the two contact points d, b are
distinct common points of ¬-intersecting circles — genuinely contradictory — so the radius facts follow
by ex falso from `step4_int : ABDC.intersectsCircle EBFD`. That intersection is proved ENTIRELY within
System E (NO new axioms), position-independent (works whether h is inside ABDC [internal] or outside
[external]):
- `m` = midpoint of chord db (via `exists_point_between_points_on_line`) is inside BOTH circles
  (`circle_points_between`).
- `w'` = the ABDC point on the centre-line GH past g is OUTSIDE EBFD. Its distance
  `|h-w'| = |g-d| + |gh|`, and the STRICT triangle inequality `|g-d| + |gh| > |h-d|` is **Euclid I.20**
  (`proposition_20`) on triangle g·h·p, where p ∈ {d,b} is whichever is off GH (at least one is, else
  the antipode structure forces g = h — `step4_int_nboth`). euclid_finish does NOT prove strict triangle
  inequalities; I.20 must be `euclid_apply`'d.
- `intersection_circle_circle_1 m w' ABDC EBFD` (m inside EBFD, w' outside EBFD, both on/inside ABDC) ⟹
  `ABDC.intersectsCircle EBFD`, contradicting ¬intersect.
KEY LESSON: no `intersectsCircle` symmetry axiom is needed (and none was added — System E untouched); the
orientation is obtained directly by choosing the circle_circle_1 witnesses (m inside, w' outside).

## Reductio-by-inconsistency steps (faithful — Euclid's impossible figure)
- Internal step5 `between b g h ∧ between g h d`: III.11@d gives `between g h d`; III.11@b gives
  `between g h b` (both contacts beyond inner centre h) — with |h-d|=|h-b|, d≠b that is contradictory, so
  `between b g h` (Euclid's BGHD figure) follows. steps 6–10 are then Euclid's genuine arithmetic FROM step5.
- External step16 `∀r between d b → r insideCircle ABDC ∧ r outsideCircle EBFD`: inside ABDC by III.2;
  outside EBFD by ex falso from `step4_int`. step17 (False) = step15(inside EBFD) vs step16(outside EBFD)
  at a midpoint r.

## Passthrough / glue nodes
step2/3 (centre facts), step11/step19 (reductio results), step13/step18 (suppositions), hpb (d=b via
step4_int) — trivial. step14 distinctPointsOnLine, step15 III.2×2 (must be `euclid_apply`'d for criterion-3).
