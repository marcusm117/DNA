import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_9 : ∀ (Y Z A B J K : Point) (j k : Circle) (YZ JB KA : Line),
  Y.isCentre j ∧
  Z.isCentre k ∧
  distinctPointsOnLine Y Z YZ ∧
  YZ.intersectsCircle j ∧ A.onLine YZ ∧ A.onCircle j ∧
  YZ.intersectsCircle k ∧ B.onLine YZ ∧ B.onCircle k ∧
  j.intersectsCircle k ∧
  J.onCircle j ∧ J.onCircle k ∧
  K.onCircle j ∧ K.onCircle k ∧
  J.opposingSides K YZ ∧
  distinctPointsOnLine J B JB ∧
  distinctPointsOnLine K A KA ∧
  ¬ JB.intersectsLine KA ∧
  ∠ Z:J:B = ∠ Y:K:A →
  (△ Z:B:J).similar (△ A:Y:K) :=
by sorry

end UniGeo.Additional
