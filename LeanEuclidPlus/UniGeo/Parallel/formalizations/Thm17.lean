import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_17 : ∀ (S V T U W : Point) (TU UW TW VS SW VW SU TV : Line),
  formTriangle T U W TU UW TW ∧
  formTriangle V S W VS SW VW ∧
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine T V TV ∧
  twoLinesIntersectAtPoint SU TV W ∧
  between S W U ∧
  between T W V ∧
  ∠ T:U:W = ∠ U:T:W ∧
  ¬ VS.intersectsLine TU →
  ∠ W:V:S = ∠ W:S:V :=
by
  euclid_intros
  have : ∠ W:S:V = ∠ T:U:W := by
    euclid_apply Elements.Book1.proposition_29''' T V U S TU VS SU
    euclid_finish
  have : ∠ U:T:W = ∠ W:V:S := by
    euclid_apply Elements.Book1.proposition_29''' U S T V TU VS TV
    euclid_finish
  euclid_finish

end UniGeo.Parallel


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- distinctPointsOnLine S V SV ∧
-- distinctPointsOnLine T U TU ∧
-- distinctPointsOnLine S U SU ∧
-- distinctPointsOnLine T V TV ∧
-- To:
-- formTriangle T U W TU UW TW ∧
-- formTriangle V S W VS SW VW ∧
-- distinctPointsOnLine S U SU ∧
-- distinctPointsOnLine T V TV ∧
