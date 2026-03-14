import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_4 : ∀ (A B C D E F G H M : Point) (AB CD AD BC EF HG EH FG AC BD : Line),
  formConvexQuadrilateral A B D C AB CD AD BC ∧
  formConvexQuadrilateral E F H G EF HG EH FG ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint AC BD M ∧
  between E A F ∧
  |(E─A)| = |(A─F)| ∧
  between F B G ∧
  |(F─B)| = |(B─G)| ∧
  between G C H ∧
  |(G─C)| = |(C─H)| ∧
  between H D E ∧
  |(H─D)| = |(D─E)| →
  between A M C ∧
  |(A─M)| = |(M─C)| ∧
  between B M D ∧
  |(B─M)| = |(M─D)| :=
by sorry

end UniGeo.Additional
