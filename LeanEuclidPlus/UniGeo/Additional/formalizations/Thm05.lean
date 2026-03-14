import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_5 : ∀ (P Q R S T U H : Point) (PQ QR RP PS QT RU : Line),
  formTriangle P Q R PQ QR RP ∧
  distinctPointsOnLine P S PS ∧ between Q S R ∧
  distinctPointsOnLine Q T QT ∧ between P T R ∧
  distinctPointsOnLine R U RU ∧ between P U Q ∧
  twoLinesIntersectAtPoint PS QR S ∧
  twoLinesIntersectAtPoint QT RP T ∧
  twoLinesIntersectAtPoint RU PQ U ∧
  twoLinesIntersectAtPoint PS RU H ∧
  twoLinesIntersectAtPoint RU QT H ∧
  ∠ P:S:Q = ∟ ∧
  ∠ Q:T:R = ∟ ∧
  ∠ R:U:P = ∟ ∧
  |(H─S)| = |(H─T)| ∧
  |(H─T)| = |(H─U)| →
  |(P─Q)| = |(Q─R)| ∧
  |(Q─R)| = |(R─P)| :=
by sorry

end UniGeo.Additional
