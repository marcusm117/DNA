import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_10 : ∀ (J K L M N O G H : Point) (JK LM NO JN OM JO NM : Line),
  distinctPointsOnLine J K JK ∧
  distinctPointsOnLine L M LM ∧
  distinctPointsOnLine N O NO ∧
  twoLinesIntersectAtPoint JK NO G ∧
  twoLinesIntersectAtPoint LM NO H ∧
  L.opposingSides N JK ∧ O.opposingSides N JK ∧
  M.opposingSides N JK ∧ H.opposingSides N JK ∧
  J.opposingSides O LM ∧ N.opposingSides O LM ∧
  K.opposingSides O LM ∧ G.opposingSides O LM ∧
  J.opposingSides K NO ∧
  J.opposingSides M NO ∧
  L.opposingSides K NO ∧
  L.opposingSides M NO →
  formConvexQuadrilateral J N O M JN OM JO NM :=
by sorry

end UniGeo.Additional
