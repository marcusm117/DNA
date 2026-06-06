import SystemE
-- A faithful proof needs Pythagoras (Book.Prop47) + Prop 2.4; deferred for now.

namespace Elements.Book2

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
  GOAL : Euclid's STATEMENT is "the square on BC is GREATER THAN the squares on BA
         and AC, BY twice rect(CA,AD)". The Greek idiom "greater than Y by Z" means
         exactly X = Y + Z (Z names the excess); the strict ordering X > Y is then
         entailed since Z = 2·rect(CA,AD) > 0. So the faithful translation is the
         single equality (the "greater" is implied, not a separate clause):
             square(BC) = square(BA) + square(AC) + 2 · rect(CA,AD)
             |b─c|·|b─c| = |b─a|·|b─a| + |a─c|·|a─c| + 2 * (|c─a| * |a─d|)
═══════════════════════════════════════════════════════════════════════════════
-/

-- Let $ABC$ be an obtuse-angled triangle, having the angle $BAC$ obtuse. And let
-- $BD$ be drawn from point $B$, perpendicular to $CA$ produced [Prop.~1.12]. I say
-- that the square on $BC$ is greater than the (sum of the) squares on $BA$ and $AC$
-- by twice the rectangle contained by $CA$ and $AD$.
theorem proposition_12 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ (∠ b:a:c : ℝ) > ∟ ∧
  d.onLine CA ∧ between d a c ∧ (∠ b:d:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| =
    |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) :=
by
  euclid_intros
  -- STATEMENT-ONLY stage: proof deferred (`sorry`). A faithful proof follows Euclid:
  -- Prop 2.4 on the cut CD, then Pythagoras [1.47] on the two right triangles △BDC,
  -- △BDA (right angle at D), with D─A─C collinear giving |DC| = |DA| + |AC|.
  -- See texts_proofs/12.txt. Correctness sanity-checked separately via 1.47.
  sorry

end Elements.Book2
