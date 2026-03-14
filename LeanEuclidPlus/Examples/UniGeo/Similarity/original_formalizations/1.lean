import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Similarity

theorem theorem_1 : ∀ (I F J H G : Point) (FI HF GI GH : Line),
  formTriangle F I J FI HF GI ∧
  formTriangle G H J GH HF GI ∧
  between I J G ∧
  between H J F ∧
  |(G─J)|/|(I─J)|= |(H─J)|/|(F─J)|→
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


-- Change Wrong Premises:
-- formTriangle F I J FI FH FH ∧
