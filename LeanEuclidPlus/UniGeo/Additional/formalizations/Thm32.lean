import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_2 : ∀ (R S T U V W X Y G : Point) (RS TU VW XY RY XS RX YS : Line),
  distinctPointsOnLine R S RS ∧
  distinctPointsOnLine T U TU ∧
  distinctPointsOnLine V W VW ∧
  distinctPointsOnLine X Y XY ∧
  G.onLine RS ∧
  G.onLine TU ∧
  G.onLine VW ∧
  G.onLine XY ∧
  V.opposingSides T XY ∧
  V.opposingSides S XY ∧
  V.opposingSides W XY ∧
  R.opposingSides T XY ∧
  R.opposingSides S XY ∧
  R.opposingSides W XY ∧
  U.opposingSides T XY ∧
  U.opposingSides S XY ∧
  U.opposingSides W XY ∧
  between X G Y ∧
  |(X─G)| = |(G─Y)| ∧
  ∠ X:R:S = ∠ X:S:R ∧
  ∠ X:S:R = ∠ Y:R:S ∧
  |(Y─R)| = |(Y─S)| →
  formConvexQuadrilateral R Y X S RY XS RX YS ∧
  |(R─Y)| = |(Y─S)| ∧
  |(Y─S)| = |(S─X)| ∧
  |(S─X)| = |(X─R)| :=
by sorry

end UniGeo.Additional
