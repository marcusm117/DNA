import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_16 : ∀ (P Q R S T : Point) (PQ QR RS ST PT PS QS : Line),
  formConvexQuadrilateral P Q S R PQ RS PS QR ∧
  distinctPointsOnLine Q S QS ∧
  T.opposingSides Q PS ∧
  distinctPointsOnLine P T PT ∧
  distinctPointsOnLine S T ST ∧
  |(S─T)| = |(R─S)| ∧
  ∠ Q:R:S = ∟ ∧
  ∠ Q:S:R = ∠ P:S:T ∧
  ∠ P:T:S = ∟ →
  |(P─T)| = |(Q─R)| :=
by
  euclid_intros
  euclid_assert (△ P:S:T).congruent (△ Q:S:R)
  euclid_finish

end UniGeo.Congruent


-- Removed the following wrong clauses:
-- Q.sameSide R PS ∧
-- P.sameSide T QS ∧

-- Removed the following clauses for a more faithful formalization of the clean text and diagram:
-- P.opposingSides R QS ∧
