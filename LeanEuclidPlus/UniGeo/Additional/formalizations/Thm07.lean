import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_7 : ∀ (W X Y Z M N Q : Point) (WX ZY WZ XY WY MN : Line),
  formConvexQuadrilateral W X Z Y WX ZY WZ XY ∧
  between W X M ∧
  between Y Z N ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine M N MN ∧
  twoLinesIntersectAtPoint WY MN Q ∧
  ¬ WX.intersectsLine ZY ∧
  |(W─Q)| = |(Y─Q)| →
  (△ W:Q:M).congruent (△ Y:Q:N) :=
by sorry

end UniGeo.Additional
