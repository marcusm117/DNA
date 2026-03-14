import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_15 : ∀ (S T U V : Point) (ST TU UV SV SU : Line),
  formConvexQuadrilateral S T V U ST UV SV TU ∧
  distinctPointsOnLine S U SU ∧
  ∠ U:V:S = ∟ ∧
  ∠ U:S:V = ∠ S:U:T ∧
  ∠ S:T:U = ∟ →
  |(U─V)| = |(S─T)| :=
by
  euclid_intros
  euclid_assert (△ S:U:V).congruent (△ U:S:T)
  euclid_finish

end UniGeo.Congruent



-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle S T U ST TU SU ∧
-- formTriangle S U V SU UV SV ∧
-- V.opposingSides T SU ∧
-- To:
-- formConvexQuadrilateral S T V U ST UV SV TU ∧
-- distinctPointsOnLine S U SU ∧
