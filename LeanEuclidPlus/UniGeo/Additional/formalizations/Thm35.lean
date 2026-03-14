import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_5 : ∀ (G H I J K L Y : Point) (GH HI IG GJ HK IL : Line),
  formTriangle G H I GH HI IG ∧
  distinctPointsOnLine G J GJ ∧ between H J I ∧
  distinctPointsOnLine H K HK ∧ between G K I ∧
  distinctPointsOnLine I L IL ∧ between G L H ∧
  twoLinesIntersectAtPoint GJ HI J ∧
  twoLinesIntersectAtPoint HK IG K ∧
  twoLinesIntersectAtPoint IL GH L ∧
  twoLinesIntersectAtPoint GJ IL Y ∧
  twoLinesIntersectAtPoint IL HK Y ∧
  ∠ G:J:H = ∟ ∧
  ∠ H:K:I = ∟ ∧
  ∠ I:L:G = ∟ ∧
  |(Y─J)| = |(Y─K)| ∧
  |(Y─K)| = |(Y─L)| →
  |(G─H)| = |(H─I)| ∧
  |(H─I)| = |(I─G)| :=
by sorry

end UniGeo.Additional
