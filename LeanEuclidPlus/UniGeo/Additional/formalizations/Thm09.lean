import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_9 : ∀ (P Q R S A B : Point) (a b : Circle) (PQ AS BR : Line),
  P.isCentre a ∧
  Q.isCentre b ∧
  distinctPointsOnLine P Q PQ ∧
  PQ.intersectsCircle a ∧ R.onLine PQ ∧ R.onCircle a ∧
  PQ.intersectsCircle b ∧ S.onLine PQ ∧ S.onCircle b ∧
  a.intersectsCircle b ∧
  A.onCircle a ∧ A.onCircle b ∧
  B.onCircle a ∧ B.onCircle b ∧
  A.opposingSides B PQ ∧
  distinctPointsOnLine A S AS ∧
  distinctPointsOnLine B R BR ∧
  ¬ AS.intersectsLine BR ∧
  ∠ Q:A:S = ∠ P:B:R →
  (△ Q:S:A).similar (△ R:P:B) :=
by sorry

end UniGeo.Additional
