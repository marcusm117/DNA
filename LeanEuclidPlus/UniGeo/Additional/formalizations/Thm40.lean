import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_10 : ∀ (R S T U V W O P : Point) (RS TU VW RV WU RW VU : Line),
  distinctPointsOnLine R S RS ∧
  distinctPointsOnLine T U TU ∧
  distinctPointsOnLine V W VW ∧
  twoLinesIntersectAtPoint RS VW O ∧
  twoLinesIntersectAtPoint TU VW P ∧
  T.opposingSides V RS ∧ W.opposingSides V RS ∧
  U.opposingSides V RS ∧ P.opposingSides V RS ∧
  R.opposingSides W TU ∧ V.opposingSides W TU ∧
  S.opposingSides W TU ∧ O.opposingSides W TU ∧
  R.opposingSides S VW ∧
  R.opposingSides U VW ∧
  T.opposingSides S VW ∧
  T.opposingSides U VW →
  formConvexQuadrilateral R V W U RV WU RW VU :=
by sorry

end UniGeo.Additional
