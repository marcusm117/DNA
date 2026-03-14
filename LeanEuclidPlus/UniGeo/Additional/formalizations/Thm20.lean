import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_10 : ∀ (F G H I J K C D : Point) (FG HI JK FJ KI FK JI : Line),
  distinctPointsOnLine F G FG ∧
  distinctPointsOnLine H I HI ∧
  distinctPointsOnLine J K JK ∧
  twoLinesIntersectAtPoint FG JK C ∧
  twoLinesIntersectAtPoint HI JK D ∧
  H.opposingSides J FG ∧ K.opposingSides J FG ∧
  I.opposingSides J FG ∧ D.opposingSides J FG ∧
  F.opposingSides K HI ∧ J.opposingSides K HI ∧
  G.opposingSides K HI ∧ C.opposingSides K HI ∧
  F.opposingSides G JK ∧
  F.opposingSides I JK ∧
  H.opposingSides G JK ∧
  H.opposingSides I JK →
  formConvexQuadrilateral F J K I FJ KI FK JI :=
by sorry

end UniGeo.Additional
