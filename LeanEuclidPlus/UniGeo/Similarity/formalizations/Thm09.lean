import SystemE
import Book.Prop15
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_9 : ∀ (P Q R S T : Point) (PR RT PT QS ST QT PS QR : Line),
  formTriangle P R T PR RT PT ∧
  formTriangle Q S T QS ST QT ∧
  distinctPointsOnLine P S PS ∧
  distinctPointsOnLine Q R QR ∧
  twoLinesIntersectAtPoint PS QR T ∧
  between P T S ∧
  between Q T R ∧
  ¬ QS.intersectsLine PR →
  (△ Q:S:T).similar (△ R:P:T) :=
by
  euclid_intros
  have : ∠ P:T:R = ∠ Q:T:S := by
    euclid_apply Elements.Book1.proposition_15 P S Q R T PS QR
    euclid_finish
  have : ∠ Q:S:T = ∠ R:P:T := by
    euclid_apply Elements.Book1.proposition_29''' Q R S P QS PR PS
    euclid_finish
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle P R T PR QR PS ∧
-- formTriangle Q S T QS PS QR ∧
-- To:
-- formTriangle P R T PR RT PT ∧
-- formTriangle Q S T QS ST QT ∧
-- distinctPointsOnLine P S PS ∧
-- distinctPointsOnLine Q R QR ∧
-- twoLinesIntersectAtPoint PS QR T ∧
