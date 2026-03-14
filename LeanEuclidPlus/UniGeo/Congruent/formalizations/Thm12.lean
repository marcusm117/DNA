import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_12 : ∀ (Q R S T U : Point) (QT TU QU RS SU RU RT QS : Line),
  formTriangle Q T U QT TU QU ∧
  formTriangle R S U RS SU RU ∧
  distinctPointsOnLine R T RT ∧
  distinctPointsOnLine Q S QS ∧
  twoLinesIntersectAtPoint RT QS U ∧
  between Q U S ∧
  between R U T ∧
  ∠ S:Q:T = ∟ ∧
  ∠ Q:S:R = ∟ ∧
  |(Q─U)| = |(S─U)| →
  (△ Q:T:U).congruent (△ S:R:U) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 R T S Q U RT QS
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle Q T U QT RT QS ∧
-- formTriangle R S U RS QS RT ∧
-- To:
-- formTriangle Q T U QT TU QU ∧
-- formTriangle R S U RS SU RU ∧
-- distinctPointsOnLine R T RT ∧
-- distinctPointsOnLine Q S QS ∧
-- twoLinesIntersectAtPoint RT QS U ∧
