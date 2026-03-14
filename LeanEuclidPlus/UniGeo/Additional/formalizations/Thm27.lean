import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_7 : ∀ (F G H I V W Z : Point) (FG IH FI GH FH VW : Line),
  formConvexQuadrilateral F G I H FG IH FI GH ∧
  between F G V ∧
  between H I W ∧
  distinctPointsOnLine F H FH ∧
  distinctPointsOnLine V W VW ∧
  twoLinesIntersectAtPoint FH VW Z ∧
  ¬ FG.intersectsLine IH ∧
  |(F─Z)| = |(H─Z)| →
  (△ F:Z:V).congruent (△ H:Z:W) :=
by sorry

end UniGeo.Additional
