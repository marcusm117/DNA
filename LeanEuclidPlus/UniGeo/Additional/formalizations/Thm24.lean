import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_4 : ∀ (J K L M N O P Q V : Point) (JK LM JM KL NO QP NQ OP JL KM : Line),
  formConvexQuadrilateral J K M L JK LM JM KL ∧
  formConvexQuadrilateral N O Q P NO QP NQ OP ∧
  distinctPointsOnLine J L JL ∧
  distinctPointsOnLine K M KM ∧
  twoLinesIntersectAtPoint JL KM V ∧
  between N J O ∧
  |(N─J)| = |(J─O)| ∧
  between O K P ∧
  |(O─K)| = |(K─P)| ∧
  between P L Q ∧
  |(P─L)| = |(L─Q)| ∧
  between Q M N ∧
  |(Q─M)| = |(M─N)| →
  between J V L ∧
  |(J─V)| = |(V─L)| ∧
  between K V M ∧
  |(K─V)| = |(V─M)| :=
by sorry

end UniGeo.Additional
