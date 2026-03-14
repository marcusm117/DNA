import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_4 : ∀ (R S T U V W X Y D : Point) (RS TU RU ST VW YX VY WX RT SU : Line),
  formConvexQuadrilateral R S U T RS TU RU ST ∧
  formConvexQuadrilateral V W Y X VW YX VY WX ∧
  distinctPointsOnLine R T RT ∧
  distinctPointsOnLine S U SU ∧
  twoLinesIntersectAtPoint RT SU D ∧
  between V R W ∧
  |(V─R)| = |(R─W)| ∧
  between W S X ∧
  |(W─S)| = |(S─X)| ∧
  between X T Y ∧
  |(X─T)| = |(T─Y)| ∧
  between Y U V ∧
  |(Y─U)| = |(U─V)| →
  between R D T ∧
  |(R─D)| = |(D─T)| ∧
  between S D U ∧
  |(S─D)| = |(D─U)| :=
by sorry

end UniGeo.Additional
