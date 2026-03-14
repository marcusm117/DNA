import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Parallel

theorem theorem_3 : ∀ (P R S Q T : Point) (PR RS SP QT : Line),
  formTriangle P R S PR RS SP ∧
  distinctPointsOnLine Q T QT ∧
  twoLinesIntersectAtPoint QT SP T ∧
  twoLinesIntersectAtPoint QT PR Q ∧
  (between P T S ∧ between P Q R) ∧
  ∠ P:T:Q = ∠ P:Q:T ∧
  ¬ QT.intersectsLine RS →
  ∠ P:S:R = ∠ Q:R:S :=
by
  euclid_intros
  have : ∠ P:S:R = ∠ P:T:Q:=by
    euclid_apply proposition_29'''' Q R P T S QT RS SP
    euclid_finish
  have : ∠ Q:R:S = ∠ P:Q:T := by
    euclid_apply proposition_29'''' T S P Q R QT RS PR
    euclid_finish
  have : ∠ Q:R:S = ∠ P:T:Q  := by euclid_finish
  have : ∠ P:S:R = ∠ Q:R:S := by euclid_finish
  euclid_finish

end UniGeo.Parallel