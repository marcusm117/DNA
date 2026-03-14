import SystemE
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_20 : ∀ (F G H I : Point) (FH FI HI GI : Line),
  formTriangle F H I FH HI FI ∧
  distinctPointsOnLine G I GI ∧
  twoLinesIntersectAtPoint GI FH G ∧
  between F G H ∧
  ∠ F:G:I = ∟ ∧
  ∠ H:I:F = ∟ →
  (△ F:H:I).similar (△ I:H:G) :=
by
  euclid_intros
  -- euclid_assert ∠ H:I:F = ∠ H:G:I
  euclid_finish

end UniGeo.Similarity

-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle F G I FH GI FI ∧
-- formTriangle G H I FH HI GI ∧
-- To:
-- formTriangle F H I FH HI FI ∧
-- distinctPointsOnLine G I GI ∧
-- twoLinesIntersectAtPoint GI FH G ∧
