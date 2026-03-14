import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_10 : ∀ (P Q R S T : Point) (PR RT PT QS SR QR PQ ST : Line),
  formTriangle P R T PR RT PT ∧
  formTriangle Q S R QS SR QR ∧
  distinctPointsOnLine P Q PQ ∧
  distinctPointsOnLine S T ST ∧
  twoLinesIntersectAtPoint PQ ST R ∧
  between P R Q ∧
  between S R T ∧
  ∠ R:P:T = ∠ R:S:Q →
  (△ P:R:T).similar (△ S:R:Q) :=
by
  euclid_intros
  have : ∠ Q:R:S = ∠ P:R:T := by
    euclid_apply Elements.Book1.proposition_15 S T P Q R ST PQ
    euclid_finish
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle P R T PQ ST PT ∧
-- formTriangle Q S R QS ST PQ ∧
-- To:
-- formTriangle P R T PR RT PT ∧
-- formTriangle Q S R QS SR QR ∧
-- distinctPointsOnLine P Q PQ ∧
-- distinctPointsOnLine S T ST ∧
-- twoLinesIntersectAtPoint PQ ST R ∧
