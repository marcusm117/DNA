import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_5 : ∀ (Y Z A B C D Q : Point) (YZ ZA AY YB ZC AD : Line),
  formTriangle Y Z A YZ ZA AY ∧
  distinctPointsOnLine Y B YB ∧ between Z B A ∧
  distinctPointsOnLine Z C ZC ∧ between Y C A ∧
  distinctPointsOnLine A D AD ∧ between Y D Z ∧
  twoLinesIntersectAtPoint YB ZA B ∧
  twoLinesIntersectAtPoint ZC AY C ∧
  twoLinesIntersectAtPoint AD YZ D ∧
  twoLinesIntersectAtPoint YB AD Q ∧
  twoLinesIntersectAtPoint AD ZC Q ∧
  ∠ Y:B:Z = ∟ ∧
  ∠ Z:C:A = ∟ ∧
  ∠ A:D:Y = ∟ ∧
  |(Q─B)| = |(Q─C)| ∧
  |(Q─C)| = |(Q─D)| →
  |(Y─Z)| = |(Z─A)| ∧
  |(Z─A)| = |(A─Y)| :=
by sorry

end UniGeo.Additional
