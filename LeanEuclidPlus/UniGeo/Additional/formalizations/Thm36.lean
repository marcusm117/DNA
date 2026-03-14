import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_6 : ∀ (R S T U V W X : Point) (RV WX : Line),
  distinctPointsOnLine R V RV ∧
  S.onLine RV ∧ T.onLine RV ∧ U.onLine RV ∧
  between R S T ∧ between S T U ∧ between T U V ∧
  |(R─T)| = |(T─V)| ∧
  |(S─T)| = |(T─U)| ∧
  distinctPointsOnLine W X WX ∧
  twoLinesIntersectAtPoint WX RV T ∧
  W.opposingSides X RV ∧
  ∠ W:T:R = ∟ ∧
  |(R─W)| = |(V─W)| →
  (△ R:S:W).congruent (△ V:U:W) :=
by sorry

end UniGeo.Additional
