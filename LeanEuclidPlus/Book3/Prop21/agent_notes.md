# Book3/Prop21 — Phase B COMPLETE (2026-07-11)

All 6 Main nodes certified (step1–5 + step5_minor). `--status`: 6/6 nodes ✓, 3/3 checks ✓.

## Structure

Main does `by_cases h_major : a.sameSide f' BD`:
- MAJOR arc (a same side as centre) — faithful Euclid: step3/4/5 via Prop 3.20 (∠BFD = 2∠BAD).
- MINOR arc (`¬a.sameSide f' BD`, the `@euclid_gap`) — `step5_minor`, proved directly.

## How the @euclid_gap (step5_minor) was resolved

The gap: Euclid's step3 claim `∠BFD = 2∠BAD` is FALSE on the minor arc (System E's [0,π]
angle model — would need a reflex angle). Earlier notes suggested this needs Prop III.22.
It does NOT. The uniform identity that holds on BOTH the minor arc AND the diameter sub-case is

    2·∠b:p:d + ∠b:f':d = 4∟   (= π - ∠BFD/2, verified numerically)

Proved for each vertex p ∈ {a, e} by `step5_minor_arc_a` / `step5_minor_arc_e` (same proof, p=a/e):
  - draw diameter through p and centre f', antipode X (`intersection_circle_line_extending_points`,
    giving `between p f' X`);
  - Prop 1.32 exterior-angle on triangles (b,p,f') and (d,p,f') extended to X ⟹ the two
    exterior angles = 2× the base (inscribed) angles;
  - foot of the ray decomposition: `by_cases f'.onLine BD` — diameter branch uses f' itself
    (`between b f' d`), minor branch constructs g = (line p f') ∩ BD with `between b g d`
    (g inside circle via `intersection_lines_opposing`);
  - `euclid_finish` assembles the linear identity in each branch (isosceles base angles are free).

step5_minor.lean then subtracts the two identities: 2∠bad + ∠bfd = 2∠bed + ∠bfd ⟹ ∠bad = ∠bed.

The diameter sub-case (f' ∈ BD, i.e. BD a diameter) IS admissible under the hypotheses (it lands in
the else branch since `a.sameSide f' BD` is false when f' is on BD), and is covered by the same lemma.

## Cleanup done
- deleted orphan `h_gap.lean` (dead node from earlier experimentation).

## Files
- step5_minor.lean (container) → step5_minor_arc_a.lean, step5_minor_arc_e.lean (leaves,
  import Book1.Prop32.Main).
