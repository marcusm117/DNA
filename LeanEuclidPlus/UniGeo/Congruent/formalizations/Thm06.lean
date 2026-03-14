import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_6 : ∀ (R S T U V : Point) (RU UV RV ST TV SV SU TR : Line),
  formTriangle S T V ST TV SV ∧
  formTriangle R U V RU UV RV ∧
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine T R TR ∧
  twoLinesIntersectAtPoint SU TR V ∧
  between R V T ∧
  between S V U ∧
  ∠ S:T:R = ∟ ∧
  |(S─T)| = |(R─U)| ∧
  ∠ U:R:T = ∟ →
  (△ S:T:V).congruent (△ U:R:V) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 R T S U V TR SU
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle R U V RU SU RT ∧
-- formTriangle S T V ST RT SU ∧
-- To:
-- formTriangle R U V RU UV RV ∧
-- formTriangle S T V ST TV SV ∧
-- distinctPointsOnLine S U SU ∧
-- distinctPointsOnLine T R TR ∧
-- twoLinesIntersectAtPoint SU TR V ∧
