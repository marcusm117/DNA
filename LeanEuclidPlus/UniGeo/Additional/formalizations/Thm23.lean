import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_3 : ∀ (G H F I Y Z : Point) (GH FI GF HI GY HZ YZ FY: Line),
  formConvexQuadrilateral G H F I GH FI GF HI ∧
  formConvexQuadrilateral G Y H Z GY HZ GH YZ ∧
  between F G Y ∧
  F.onLine FY ∧ G.onLine FY ∧ Y.onLine FY ∧
  ∠ F:G:H = ∟ ∧
  ¬ GH.intersectsLine FI ∧
  ∠ I:F:H = ∠ H:Y:G →
  (△ H:Y:G).similar (△ F:H:G) :=
by sorry

end UniGeo.Additional
