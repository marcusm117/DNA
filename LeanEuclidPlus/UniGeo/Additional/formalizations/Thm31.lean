import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_1 : ∀ (R S T U V W X : Point) (RS ST UT UV VR RT RU SV : Line),
  distinctPointsOnLine R S RS ∧
  distinctPointsOnLine S T ST ∧
  distinctPointsOnLine T U UT ∧
  distinctPointsOnLine U V UV ∧
  distinctPointsOnLine V R VR ∧
  R.sameSide S UV ∧ S.sameSide T UV ∧
  S.sameSide T VR ∧ T.sameSide U VR ∧
  T.sameSide U RS ∧ U.sameSide V RS ∧
  U.sameSide V ST ∧ V.sameSide R ST ∧
  V.sameSide R UT ∧ R.sameSide S UT ∧
  distinctPointsOnLine R T RT ∧
  distinctPointsOnLine R U RU ∧
  distinctPointsOnLine S V SV ∧
  twoLinesIntersectAtPoint RT SV W ∧
  twoLinesIntersectAtPoint RU SV X ∧
  between V X W ∧
  |(V─X)| = |(X─W)| ∧
  between X W S ∧
  |(X─W)| = |(W─S)| ∧
  ∠ S:R:T = ∠ V:R:U ∧
  |(R─S)| = |(R─V)| →
  (△ R:S:W).congruent (△ R:V:X) :=
by sorry

end UniGeo.Additional
