import SystemE
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_16 : ∀ (Q R S T U : Point) (RT TU RU QS SU QU : Line),
  formTriangle R T U RT TU RU ∧
  formTriangle Q S U QS SU QU ∧
  twoLinesIntersectAtPoint RT SU R ∧
  twoLinesIntersectAtPoint RT QU T ∧
  between Q T U ∧
  between S R U ∧
  |(R─U)| / |(S─U)| = |(T─U)| / |(Q─U)| →
  (△ R:T:U).similar (△ S:Q:U) :=
by
  euclid_intros

  have : ∠ R:U:T = ∠ S:U:Q := by
    euclid_finish
  apply Triangle.similar_sas (△ R:T:U) (△ S:Q:U)

  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle Q S U QS SU QU ∧
-- formTriangle R T U RT QU SU ∧
-- To:
-- formTriangle R T U RT TU RU ∧
-- formTriangle Q S U QS SU QU ∧
-- twoLinesIntersectAtPoint RT SU R ∧
-- twoLinesIntersectAtPoint RT QU T ∧
