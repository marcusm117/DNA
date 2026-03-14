import SystemE
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_8 : ∀ (G H I J K : Point) (GH GI HI GJ KJ GK : Line),
  formTriangle G H I GH HI GI ∧
  formTriangle G J K GJ KJ GK ∧
  twoLinesIntersectAtPoint KJ GI K ∧
  twoLinesIntersectAtPoint KJ GH J ∧
  between G K I ∧
  between G J H ∧
  |(G─J)| / |(G─H)| = |(G─K)| / |(G─I)| →
  (△ G:J:K).similar (△ G:H:I) :=
by
  euclid_intros
  apply Triangle.similar_sas (△ G:J:K) (△ G:H:I)
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle G J K GH JK GI ∧
-- To:
-- formTriangle G J K GJ KJ GK ∧
-- twoLinesIntersectAtPoint KJ GI K ∧
-- twoLinesIntersectAtPoint KJ GH J ∧
