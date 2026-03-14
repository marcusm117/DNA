import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_1 : ∀ (J K L M N O P : Point) (JK KL ML MN NJ JL JM KN : Line),
  distinctPointsOnLine J K JK ∧
  distinctPointsOnLine K L KL ∧
  distinctPointsOnLine L M ML ∧
  distinctPointsOnLine M N MN ∧
  distinctPointsOnLine N J NJ ∧
  J.sameSide K MN ∧ K.sameSide L MN ∧
  K.sameSide L NJ ∧ L.sameSide M NJ ∧
  L.sameSide M JK ∧ M.sameSide N JK ∧
  M.sameSide N KL ∧ N.sameSide J KL ∧
  N.sameSide J ML ∧ J.sameSide K ML ∧
  distinctPointsOnLine J L JL ∧
  distinctPointsOnLine J M JM ∧
  distinctPointsOnLine K N KN ∧
  twoLinesIntersectAtPoint JL KN O ∧
  twoLinesIntersectAtPoint JM KN P ∧
  between N P O ∧
  |(N─P)| = |(P─O)| ∧
  between P O K ∧
  |(P─O)| = |(O─K)| ∧
  ∠ K:J:L = ∠ N:J:M ∧
  |(J─K)| = |(J─N)| →
  (△ J:K:O).congruent (△ J:N:P) :=
by sorry

end UniGeo.Additional
