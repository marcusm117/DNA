import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_11 : ∀ (Q T R S U : Point) (QT TU QU RS SU RU QS RT : Line),
  formTriangle R S U RS SU RU ∧
  formTriangle Q T U QT TU QU ∧
  distinctPointsOnLine Q S QS ∧
  distinctPointsOnLine R T RT ∧
  twoLinesIntersectAtPoint QS RT U ∧
  between Q U S ∧
  between R U T ∧
  ¬ RS.intersectsLine QT ∧
  ∠ T:Q:U = ∠ Q:T:U →
  ∠ R:S:U = ∠ S:R:U :=
by
  euclid_intros
  have : ∠ T:Q:U = ∠ R:S:U := by
    euclid_apply Elements.Book1.proposition_29''' R T S Q RS QT QS
    euclid_finish
  have : ∠ S:R:U = ∠ Q:T:U := by
    euclid_apply Elements.Book1.proposition_29''' Q S T R QT RS RT
    euclid_finish
  euclid_finish

end UniGeo.Parallel


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- distinctPointsOnLine Q T QT ∧
-- distinctPointsOnLine R S RS ∧
-- To:
-- formTriangle Q T U QT TU QU ∧
-- formTriangle R S U RS SU RU ∧
-- distinctPointsOnLine Q S QS ∧
-- distinctPointsOnLine R T RT ∧
