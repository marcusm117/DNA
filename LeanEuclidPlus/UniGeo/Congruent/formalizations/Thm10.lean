import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_10 : ∀ (Q R S T U : Point) (QT TU QU RS SU RU QS RT : Line),
  formTriangle Q T U QT TU QU ∧
  formTriangle R S U RS SU RU ∧
  distinctPointsOnLine Q S QS ∧
  distinctPointsOnLine R T RT ∧
  twoLinesIntersectAtPoint QS RT U ∧
  between Q U S ∧
  between R U T ∧
  ∠ R:S:Q = ∟ ∧
  ∠ S:Q:T = ∟ ∧
  |(S─U)| = |(Q─U)| →
  (△ R:S:U).congruent (△ T:Q:U) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 Q S T R U QS RT
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle Q T U QT RT QS ∧
-- formTriangle R S U RS QS RT ∧
-- To:
-- formTriangle Q T U QT TU QU ∧
-- formTriangle R S U RS SU RU ∧
-- distinctPointsOnLine Q S QS ∧
-- distinctPointsOnLine R T RT ∧
-- twoLinesIntersectAtPoint QS RT U ∧
