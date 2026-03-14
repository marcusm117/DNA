import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_2 : ∀ (F G H I J K L M U : Point) (FG HI JK LM FM LG FL MG : Line),
  distinctPointsOnLine F G FG ∧
  distinctPointsOnLine H I HI ∧
  distinctPointsOnLine J K JK ∧
  distinctPointsOnLine L M LM ∧
  U.onLine FG ∧
  U.onLine HI ∧
  U.onLine JK ∧
  U.onLine LM ∧
  J.opposingSides H LM ∧
  J.opposingSides G LM ∧
  J.opposingSides K LM ∧
  F.opposingSides H LM ∧
  F.opposingSides G LM ∧
  F.opposingSides K LM ∧
  I.opposingSides H LM ∧
  I.opposingSides G LM ∧
  I.opposingSides K LM ∧
  between L U M ∧
  |(L─U)| = |(U─M)| ∧
  ∠ L:F:G = ∠ L:G:F ∧
  ∠ L:G:F = ∠ M:F:G ∧
  |(M─F)| = |(M─G)| →
  formConvexQuadrilateral F M L G FM LG FL MG ∧
  |(F─M)| = |(M─G)| ∧
  |(M─G)| = |(G─L)| ∧
  |(G─L)| = |(L─F)| :=
by sorry

end UniGeo.Additional
