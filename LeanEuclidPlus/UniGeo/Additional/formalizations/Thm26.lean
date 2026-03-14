import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_6 : ∀ (J K L M N O P : Point) (JN OP : Line),
  distinctPointsOnLine J N JN ∧
  K.onLine JN ∧ L.onLine JN ∧ M.onLine JN ∧
  between J K L ∧ between K L M ∧ between L M N ∧
  |(J─L)| = |(L─N)| ∧
  |(K─L)| = |(L─M)| ∧
  distinctPointsOnLine O P OP ∧
  twoLinesIntersectAtPoint OP JN L ∧
  O.opposingSides P JN ∧
  ∠ O:L:J = ∟ ∧
  |(J─O)| = |(N─O)| →
  (△ J:K:O).congruent (△ N:M:O) :=
by sorry

end UniGeo.Additional
