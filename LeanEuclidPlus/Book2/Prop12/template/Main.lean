import SystemE
import Book.Prop47      -- 1.47 Pythagoras

namespace Elements.Book2

open Elements.Book1

/-
═══════════════════════════════════════════════════════════════════════════════
STATEMENT — Prop 2.12   (obtuse "law of cosines")
Convention: "square on X"              = |X|·|X|
            "rectangle contained by X,Y" = |X|·|Y|
            "twice R"                   = 2 * R
            (LeanEuclid, cf. Book 1 Prop 47/48; matches Book2/Prop01).
───────────────────────────────────────────────────────────────────────────────
In obtuse-angled triangles, the square on the side subtending the obtuse angle is
greater than the (sum of the) squares on the sides containing the obtuse angle by
twice the (rectangle) contained by one of the sides around the obtuse angle, to
which a perpendicular (straight-line) falls, and the (straight-line) cut off
outside (the triangle) by the perpendicular towards the obtuse angle.

  layout   : D ── A ── C   collinear (A between D and C); B off line CA.
             Triangle ABC, obtuse at A; BD ⊥ CA produced, foot D beyond A.
  premises : formTriangle a b c AB BC CA;  ∠ b:a:c > ∟  (obtuse at A);
             d.onLine CA ∧ between d a c ∧ ∠ b:d:c = ∟  (BD ⊥ CA produced at D)
  GOAL : square(BC) = square(BA) + square(AC) + 2 · rect(CA,AD)
         |b─c|·|b─c| = |b─a|·|b─a| + |a─c|·|a─c| + 2 * (|c─a| * |a─d|)
═══════════════════════════════════════════════════════════════════════════════

PROOF (non-faithful but valid).  Draw BD (the given perpendicular line) and apply
Pythagoras [1.47] to the two right triangles sharing the leg BD:
    △BDC (right at D):  |bc|² = |bd|² + |dc|²
    △BDA (right at D):  |ba|² = |bd|² + |da|²
D─A─C collinear (between d a c) gives  |dc| = |da| + |ac|.  Substituting and
expanding,  |bc|² = |ba|² + |ac|² + 2·|da|·|ac| = |ba|² + |ac|² + 2·|ca|·|ad|.
The closing step is a `ring` identity (the SMT translator cannot handle the `2*`
in the goal, so it is discharged in pure Lean once the lengths are pinned).
-/

-- Let $ABC$ be an obtuse-angled triangle, having the angle $BAC$ obtuse. And let
-- $BD$ be drawn from point $B$, perpendicular to $CA$ produced [Prop.~1.12]. I say
-- that the square on $BC$ is greater than the (sum of the) squares on $BA$ and $AC$
-- by twice the rectangle contained by $CA$ and $AD$.
set_option systemE.solverTime 30 in
theorem proposition_12 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ (∠ b:a:c : ℝ) > ∟ ∧
  d.onLine CA ∧ between d a c ∧ (∠ b:d:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| =
    |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) :=
by
  euclid_intros
  -- the perpendicular line BD
  euclid_apply (line_from_points b d) as BD
  -- Pythagoras on the two right triangles (right angle at D)
  euclid_apply (proposition_47 d b c BD BC CA)   -- |bc|² = |bd|² + |dc|²
  euclid_apply (proposition_47 d b a BD AB CA)   -- |ba|² = |bd|² + |da|²
  have h1 : |(b─c)| * |(b─c)| = |(b─d)| * |(b─d)| + |(d─c)| * |(d─c)| := by euclid_finish
  have h2 : |(b─a)| * |(b─a)| = |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| := by euclid_finish
  -- D─A─C collinear  ⟹  |dc| = |da| + |ac|
  have hdc : |(d─c)| = |(d─a)| + |(a─c)| := by euclid_finish
  have hda : |(d─a)| = |(a─d)| := by euclid_finish
  have hac : |(a─c)| = |(c─a)| := by euclid_finish
  rw [h1, h2, hdc, hda, hac]; ring

end Elements.Book2
