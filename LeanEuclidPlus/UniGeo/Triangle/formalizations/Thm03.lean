import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_3 : ∀ (H I J K : Point) (HI IJ JH HK : Line),
  formTriangle H I J HI IJ JH ∧
  distinctPointsOnLine H K HK ∧
  twoLinesIntersectAtPoint HK IJ K ∧
  between I K J ∧
  ∠ I:H:K = ∠ J:H:K ∧
  |(H─I)| = |(H─J)| →
  ∠ H:K:I = ∠ H:K:J :=
by
  euclid_intros
  euclid_assert (△ H:I:K).congruent (△ H:J:K)
  euclid_finish

end UniGeo.Triangle


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- IJ.intersectsLine HK ∧ K.onLine IJ
-- To:
-- twoLinesIntersectAtPoint HK IJ K
