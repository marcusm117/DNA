import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_4 : ∀ (F G H I J K L M R : Point) (FG HI FI GH JK ML JM KL FH GI : Line),
  formConvexQuadrilateral F G I H FG HI FI GH ∧
  formConvexQuadrilateral J K M L JK ML JM KL ∧
  distinctPointsOnLine F H FH ∧
  distinctPointsOnLine G I GI ∧
  twoLinesIntersectAtPoint FH GI R ∧
  between J F K ∧
  |(J─F)| = |(F─K)| ∧
  between K G L ∧
  |(K─G)| = |(G─L)| ∧
  between L H M ∧
  |(L─H)| = |(H─M)| ∧
  between M I J ∧
  |(M─I)| = |(I─J)| →
  between F R H ∧
  |(F─R)| = |(R─H)| ∧
  between G R I ∧
  |(G─R)| = |(R─I)| :=
by sorry

end UniGeo.Additional
