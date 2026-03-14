import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_10 : ∀ (A B C D E F X Y : Point) (AB CD EF AE FD AF ED : Line),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint AB EF X ∧
  twoLinesIntersectAtPoint CD EF Y ∧
  C.opposingSides E AB ∧ F.opposingSides E AB ∧
  D.opposingSides E AB ∧ Y.opposingSides E AB ∧
  A.opposingSides F CD ∧ E.opposingSides F CD ∧
  B.opposingSides F CD ∧ X.opposingSides F CD ∧
  A.opposingSides B EF ∧
  A.opposingSides D EF ∧
  C.opposingSides B EF ∧
  C.opposingSides D EF →
  formConvexQuadrilateral A E F D AE FD AF ED :=
by sorry

end UniGeo.Additional
