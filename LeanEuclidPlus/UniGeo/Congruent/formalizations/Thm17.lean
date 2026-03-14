import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_17 : ∀ (R S T U V : Point) (RU UV RV ST TV SV SU RT : Line),
  formTriangle R U V RU UV RV ∧
  formTriangle S T V ST TV SV ∧
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine R T RT ∧
  twoLinesIntersectAtPoint SU RT V ∧
  between S V U ∧
  between R V T ∧
  |(U─V)| = |(T─V)| ∧
  |(S─V)| = |(R─V)| →
  |(R─U)| = |(S─T)| :=
by
  euclid_intros
  have : ∠ R:V:U = ∠ S:V:T := by
    euclid_apply Elements.Book1.proposition_15 R T U S V RT SU
    euclid_finish
  euclid_assert (△ R:U:V).congruent (△ S:T:V)
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle R U V RU SU RT ∧
-- formTriangle S T V ST RT SU ∧
-- To:
-- formTriangle R U V RU UV RV ∧
-- formTriangle S T V ST TV SV ∧
-- distinctPointsOnLine S U SU ∧
-- distinctPointsOnLine R T RT ∧
-- twoLinesIntersectAtPoint SU RT V ∧
