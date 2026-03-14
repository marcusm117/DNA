import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Similarity

theorem theorem_1 : ∀ (G H J I F : Point) (GH HJ JG IF FJ JI HF GI : Line),
  formTriangle G H J GH HJ JG ∧
  formTriangle I F J IF FJ JI ∧
  distinctPointsOnLine H F HF ∧
  distinctPointsOnLine G I GI ∧
  twoLinesIntersectAtPoint GI HF J ∧
  between G J I ∧
  between H J F ∧
  |(G─J)| / |(I─J)| = |(H─J)| / |(F─J)| →
  (△ G:H:J).similar (△ I:F:J) :=
by
  euclid_intros
  have : G ≠ H ∧ H ≠ J ∧ G ≠ J ∧ (△ G:H:J).area > 0 := by
    euclid_finish
  have : I ≠ F ∧ F ≠ J ∧ I ≠ J ∧ (△ I:F:J).area > 0 := by
    euclid_finish
  have : ∠ H:J:G = ∠ F:J:I := by
    euclid_apply proposition_15 I G F H J GI HF
    euclid_finish
  have : |(H─J)| / |(F─J)| = |(G─J)| / |(I─J)| := by
    euclid_finish
  euclid_finish

end UniGeo.Similarity