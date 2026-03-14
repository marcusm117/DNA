import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_7 : ∀ (N O P Q D E H : Point) (NO QP NQ OP NP DE : Line),
  formConvexQuadrilateral N O Q P NO QP NQ OP ∧
  between N O D ∧
  between P Q E ∧
  distinctPointsOnLine N P NP ∧
  distinctPointsOnLine D E DE ∧
  twoLinesIntersectAtPoint NP DE H ∧
  ¬ NO.intersectsLine QP ∧
  |(N─H)| = |(P─H)| →
  (△ N:H:D).congruent (△ P:H:E) :=
by sorry

end UniGeo.Additional
