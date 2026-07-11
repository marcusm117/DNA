# Prop13 (III.13) — implementation plan (blocked on Prop11 completion)

Prop13/step4 imports Book3.Prop11.Main and cites III.11; nothing past step4 certifies until III.11 is
sorry-free. step4 itself is written & builds. Steps 5–19 are designed below; implement + test when unblocked.

## ⚠ RISK introduced by the III.11 signature fix — verify step4 FIRST
proposition_11 gained hypothesis `|(g─a)| < |(f─a)|` (inner radius < outer). step4 calls
`proposition_11 d g h ABDC EBFD` and `proposition_11 b g h ABDC EBFD`, so it must now ALSO supply
`|(h─d)| < |(g─d)|` and `|(h─b)| < |(g─b)|` (r_EBFD < r_ABDC at each contact). This is a containment-flavored
fact (EBFD ⊆ ABDC ⟹ r_EBFD ≤ r_ABDC − |gh| < r_ABDC). NOT obviously euclid_finish-able from
`h.insideCircle ABDC` alone. Options if it's hard: (a) derive via ¬intersect + the interior point h with a
circle_points_extend-style argument; (b) reconsider whether the reductio's two-contact-point inconsistency
discharges it. TEST step4 immediately once Prop11 builds; if blocked, this is the first thing to solve.

## Internal case (inside habsurd1) — steps 5–11
Geometry: III.11 at BOTH contacts gives `between g h d` (g-h-d) AND `between g h b` (g-h-b) — both contacts
beyond inner centre h. With |h-d|=|h-b|=r_EBFD and d≠b that's ALREADY contradictory (two pts beyond h at
equal radius ⟹ d=b). So steps 5–10 live in an inconsistent context (Euclid's genuine reductio); each is
provable once the III.11 betweenness facts + radii are in scope.
- step5 `between b g h ∧ between g h d`: between g h d from III.11@d directly; between b g h only via the
  inconsistency (III.11@b gives g-h-b, opposite) — supply III.11 at both + radii, euclid_finish (ex falso).
  NOTE: this is the flagged "provable-by-inconsistency" shape; it is faithful (Euclid asserts BGHD off the
  impossible figure). Backing file: euclid_apply proposition_11 twice, then euclid_finish.
- step6 `|(b─g)| = |(g─d)|`: radii of ABDC (g centre, b,d on ABDC). euclid_finish from g.isCentre + on-circle.
- step7 `|(b─g)| > |(h─d)|`: with between g h d, |g-d| = |g-h|+|h-d| > |h-d|; and |b-g|=|g-d| (step6). euclid_finish[step5,step6].
- step8 `|(b─h)| > |(h─d)|`: with between b g h (or via inconsistency), |b-h| = |b-g|+|g-h| > |b-g| = |g-d| > |h-d|. euclid_finish[step5,step6,step7].
- step9 `|(b─h)| = |(h─d)|`: radii of EBFD (h centre). euclid_finish.
- step10 `False`: step8 (|bh|>|hd|) vs step9 (|bh|=|hd|). euclid_finish[step8,step9] or linarith.
- step11 `¬(d≠b ∧ h.insideCircle ABDC)`: the reductio result = habsurd1 passthrough.

## External case (inside habsurd2) — steps 13–18
- step13 `d≠b ∧ h.outsideCircle ABDC`: hsuppose2 passthrough.
- step14 `distinctPointsOnLine d b AC`: from line_from_points d b (d≠b). euclid_finish.
- step15 `∀ r, between d r b → r.insideCircle ABDC ∧ r.insideCircle EBFD`: III.2 (proposition_2 Book3) on
  each circle — d,b on ABDC ⟹ chord inside ABDC; d,b on EBFD ⟹ chord inside EBFD. euclid_apply proposition_2 twice.
- step16 `∀ r, between d r b → r.insideCircle ABDC ∧ r.outsideCircle EBFD`: Def 3.3 (external tangency ⟹
  the chord of ABDC lies outside EBFD). This is the subtle one — needs the external-touch geometry. Likely
  needs a construction/euclid_gap; study Book3/Prop12 (external twin) for the pattern.
- step17 `False`: instantiate step15 & step16 at some r with between d r b (exists via
  exists_point_between_points_on_line on AC, d≠b) → r.insideCircle EBFD ∧ r.outsideCircle EBFD. euclid_finish.
- step18 `¬(d≠b ∧ h.outsideCircle ABDC)`: reductio result (habsurd2 passthrough).

## Tail — step19, hpb
- step19 `¬(d≠b ∧ h.insideCircle ABDC)`: restate step11.
- hpb `d = b`: from step18 + step19 (h is either inside or outside ABDC — trichotomy needs h≠on; or the two
  ¬-facts cover both cases) ⟹ ¬(d≠b) ⟹ d=b. Check how the two habsurds combine to force d=b (may need
  h.insideCircle ∨ h.outsideCircle ∨ h.onCircle case analysis).

## Cited props needed built & sorry-free: III.1 (proposition_1 — construction, done?), III.2 (proposition_2),
## III.11 (proposition_11 — in progress). Verify each is sorry-free or step*/P will fail transitively.
