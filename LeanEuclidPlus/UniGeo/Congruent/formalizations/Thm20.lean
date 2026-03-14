import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_20 : ∀ (F G H I J : Point) (FH FI IG GJ JH : Line),
  formTriangle F I G FI IG FH ∧
  formTriangle G J H GJ JH FH ∧
  between F G H ∧
  I.sameSide J FH ∧ I ≠ J ∧
  |(F─G)| = |(H─G)| ∧
  |(G─J)| = |(F─I)| ∧
  |(G─I)| = |(H─J)| →
  ∠ G:J:H = ∠ F:I:G :=
by
  euclid_intros
  euclid_assert (△ F:G:I).congruent (△ G:H:J)
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- I.sameSide J FH ∧
-- To:
-- I.sameSide J FH ∧ I ≠ J
