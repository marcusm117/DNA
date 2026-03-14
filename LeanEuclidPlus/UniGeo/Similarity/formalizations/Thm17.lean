import SystemE
import Book.Prop32
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_17 : ∀ (G H I J : Point) (GJ IJ GI JH : Line),
  formTriangle G J I GJ IJ GI ∧
  distinctPointsOnLine J H JH ∧
  twoLinesIntersectAtPoint JH GI H ∧
  between G H I ∧
  ∠ G:J:I = ∟ ∧
  ∠ J:H:I = ∟ →
  (△ H:I:J).similar (△ H:J:G) :=
by
  euclid_intros
  -- euclid_assert ∠ I:H:J = ∠ G:H:J
  have : ∠ I:G:J + ∠ G:I:J = ∟ := by
    euclid_apply extend_point GI G I as X
    euclid_apply Elements.Book1.proposition_32 J G I X GJ GI IJ
    euclid_finish
  have : ∠ I:G:J + ∠ G:J:H = ∟ := by
    euclid_apply extend_point GJ G J as Y
    euclid_apply Elements.Book1.proposition_32 H G J Y GI GJ JH
    euclid_finish
  -- euclid_assert ∠ G:J:H = ∠ G:I:J
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle G H J GI JH GJ ∧
-- formTriangle H I J GI IJ JH ∧
-- To:
-- formTriangle G J I GJ IJ GI ∧
-- distinctPointsOnLine H J JH ∧
-- twoLinesIntersectAtPoint JH GI H ∧
