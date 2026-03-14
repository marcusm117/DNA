import SystemE
import Book.Prop15
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_5 : ∀ (F G H I J : Point) (GH HJ GJ FI IJ FJ HF GI : Line),
  formTriangle G H J GH HJ GJ ∧
  formTriangle F I J FI IJ FJ ∧
  distinctPointsOnLine H F HF ∧
  distinctPointsOnLine G I GI ∧
  twoLinesIntersectAtPoint HF GI J ∧
  between F J H ∧
  between G J I ∧
  ¬ FI.intersectsLine GH →
  (△ F:I:J).similar (△ H:G:J) :=
by
  euclid_intros
  have : ∠ G:J:H = ∠ F:J:I := by
    euclid_apply Elements.Book1.proposition_15 G I H F J GI HF
    euclid_finish
  have : ∠ J:F:I = ∠ G:H:J := by
    euclid_apply Elements.Book1.proposition_29''' G I H F GH FI HF
    euclid_finish
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle F I J FI GI FH ∧
-- formTriangle G H J GH FH GI ∧
-- To:
-- formTriangle G H J GH HJ GJ ∧
-- formTriangle F I J FI IJ FJ ∧
-- distinctPointsOnLine H F HF ∧
-- distinctPointsOnLine G I GI ∧
-- twoLinesIntersectAtPoint HF GI J ∧
