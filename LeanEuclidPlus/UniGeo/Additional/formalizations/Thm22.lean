import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_2 : ∀ (J K L M N O P Q Y : Point) (JK LM NO PQ JQ PK JP QK : Line),
  distinctPointsOnLine J K JK ∧
  distinctPointsOnLine L M LM ∧
  distinctPointsOnLine N O NO ∧
  distinctPointsOnLine P Q PQ ∧
  Y.onLine JK ∧
  Y.onLine LM ∧
  Y.onLine NO ∧
  Y.onLine PQ ∧
  N.opposingSides L PQ ∧
  N.opposingSides K PQ ∧
  N.opposingSides O PQ ∧
  J.opposingSides L PQ ∧
  J.opposingSides K PQ ∧
  J.opposingSides O PQ ∧
  M.opposingSides L PQ ∧
  M.opposingSides K PQ ∧
  M.opposingSides O PQ ∧
  between P Y Q ∧
  |(P─Y)| = |(Y─Q)| ∧
  ∠ P:J:K = ∠ P:K:J ∧
  ∠ P:K:J = ∠ Q:J:K ∧
  |(Q─J)| = |(Q─K)| →
  formConvexQuadrilateral J Q P K JQ PK JP QK ∧
  |(J─Q)| = |(Q─K)| ∧
  |(Q─K)| = |(K─P)| ∧
  |(K─P)| = |(P─J)| :=
by sorry

end UniGeo.Additional
