import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_13 : ∀ (G H I J K : Point) (GJ JH GH HK KI HI IG : Line),
  formTriangle G J H GJ JH GH ∧
  formTriangle H K I HK KI HI ∧
  between G H I ∧
  distinctPointsOnLine I G IG ∧
  J.sameSide K IG ∧ J ≠ K ∧
  |(G─J)| = |(H─K)| ∧
  ∠ H:K:I = ∠ G:J:H ∧
  ¬ GJ.intersectsLine HK →
  (△ H:I:K).congruent (△ G:H:J) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29'''' K J I H G HK GJ IG
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle F I G FI IG FH ∧
-- formTriangle G J H GJ JH FH ∧
-- J.sameSide K IG ∧
-- To:
-- formTriangle G J H GJ JH GH ∧
-- formTriangle H K I HK KI HI ∧
-- distinctPointsOnLine I G IG ∧
-- J.sameSide K IG ∧ J ≠ K ∧
