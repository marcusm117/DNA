import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_6 : ∀ (F G H I J K L : Point) (FJ KL : Line),
  distinctPointsOnLine F J FJ ∧
  G.onLine FJ ∧ H.onLine FJ ∧ I.onLine FJ ∧
  between F G H ∧ between G H I ∧ between H I J ∧
  |(F─H)| = |(H─J)| ∧
  |(G─H)| = |(H─I)| ∧
  distinctPointsOnLine K L KL ∧
  twoLinesIntersectAtPoint KL FJ H ∧
  K.opposingSides L FJ ∧
  ∠ K:H:F = ∟ ∧
  |(F─K)| = |(J─K)| →
  (△ F:G:K).congruent (△ J:I:K) :=
by sorry

end UniGeo.Additional
