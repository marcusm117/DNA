import SystemE

namespace Elements.Book3

-- "Similar segments of circles on equal straight-lines are equal to one another."
-- Proof-faithful form (post-superposition): after applying segment AEB onto CFD (placing A on C,
-- B on D — valid since |AB|=|CD|), both circles share the chord endpoints a, b on line AB.
-- "Similar segments" = equal inscribed angles on the same side (∠a:e:b = ∠a:f:b, e.sameSide f AB).
-- Conclusion: AEB = CFD (the circles coincide [C.N.4], established by the III.10 reductio).
-- Proof sentence map:
--   S1 "B will also coincide with D": b.onCircle AEB ∧ b.onCircle CFD — given directly
--      (both circles share endpoint b after placing a on c and AB on CD).
--   S2 "the segment AEB will also coincide with CFD": main claim → AEB = CFD.
--   S3 reductio via [Prop.~3.10]: assume AEB ≠ CFD; a and b are on both circles (2 shared
--      points); if the arc of AEB misses / falls inside / outside CFD, it crosses CFD's arc
--      at a third point, giving 3 common points on two distinct circles → ⊥ by Prop.~3.10.
--   S4 "will coincide, and will be equal [C.N.4]": AEB = CFD closes the goal.
-- Endpoint well-posedness: no sameSide in the conclusion; a and b lie ON AB (not sameSide e AB),
-- but they appear only in onCircle / distinctPointsOnLine hypotheses, never in a sameSide goal.
-- orchestrator-FIXED: replaced the ill-posed ∀p·(onCircle AEB ∧ sameSide e AB) ↔ (onCircle CFD ∧ sameSide f CD)
-- biconditional (false at p=a,b since a,b ∈ AB) with the post-superposition AEB = CFD statement.
theorem proposition_24 : ∀ (a e b f : Point) (AB : Line) (AEB CFD : Circle),
  a.onCircle AEB ∧ e.onCircle AEB ∧ b.onCircle AEB ∧
  a.onCircle CFD ∧ f.onCircle CFD ∧ b.onCircle CFD ∧
  distinctPointsOnLine a b AB ∧
  ¬ e.onLine AB ∧ ¬ f.onLine AB ∧
  e.sameSide f AB ∧
  ∠ a:e:b = ∠ a:f:b →
  AEB = CFD :=
by
  sorry

end Elements.Book3
