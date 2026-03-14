import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_1 : ∀ (F G H I J K L : Point) (FG GH IH IJ JF FH FI GJ : Line),
  distinctPointsOnLine F G FG ∧
  distinctPointsOnLine G H GH ∧
  distinctPointsOnLine H I IH ∧
  distinctPointsOnLine I J IJ ∧
  distinctPointsOnLine J F JF ∧
  F.sameSide G IJ ∧ G.sameSide H IJ ∧
  G.sameSide H JF ∧ H.sameSide I JF ∧
  H.sameSide I FG ∧ I.sameSide J FG ∧
  I.sameSide J GH ∧ J.sameSide F GH ∧
  J.sameSide F IH ∧ F.sameSide G IH ∧
  distinctPointsOnLine F H FH ∧
  distinctPointsOnLine F I FI ∧
  distinctPointsOnLine G J GJ ∧
  twoLinesIntersectAtPoint FH GJ K ∧
  twoLinesIntersectAtPoint FI GJ L ∧
  between J L K ∧
  |(J─L)| = |(L─K)| ∧
  between L K G ∧
  |(L─K)| = |(K─G)| ∧
  ∠ G:F:H = ∠ J:F:I ∧
  |(F─G)| = |(F─J)| →
  (△ F:G:K).congruent (△ F:J:L) :=
by sorry

end UniGeo.Additional
