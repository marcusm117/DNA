import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_7 : ∀ (B C D E R S V : Point) (BC ED BE CD BD RS : Line),
  formConvexQuadrilateral B C E D BC ED BE CD ∧
  between B C R ∧
  between D E S ∧
  distinctPointsOnLine B D BD ∧
  distinctPointsOnLine R S RS ∧
  twoLinesIntersectAtPoint BD RS V ∧
  ¬ BC.intersectsLine ED ∧
  |(B─V)| = |(D─V)| →
  (△ B:V:R).congruent (△ D:V:S) :=
by sorry

end UniGeo.Additional
