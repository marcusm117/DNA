import SystemE
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_3 : ∀ (W X Y Z : Point) (WX YZ XY WZ WY : Line),
  formConvexQuadrilateral W X Z Y WX YZ WZ XY ∧
  distinctPointsOnLine W Y WY ∧
  |(X─Y)| = |(W─Z)| ∧
  |(Y─Z)| = |(W─X)| →
  ∠ Y:W:Z = ∠ W:Y:X :=
by
  euclid_intros
  euclid_assert (△ W:X:Y).congruent (△ Y:Z:W)
  euclid_finish

end UniGeo.Quadrilateral
