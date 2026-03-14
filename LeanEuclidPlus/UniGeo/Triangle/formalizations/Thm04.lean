import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_4 : ∀ (U V W X : Point) (UV VW WU UX : Line),
  formTriangle U V W UV VW WU ∧
  distinctPointsOnLine U X UX ∧
  twoLinesIntersectAtPoint UX VW X ∧
  between V X W ∧
  ∠ U:V:W = ∠ U:W:V ∧
  ∠ U:X:V = ∟ ∧ ∠ U:X:W = ∟ →
  |(U─W)| = |(U─V)| :=
by
  euclid_intros
  euclid_assert (△ U:V:X).congruent (△ U:W:X)
  euclid_finish

end UniGeo.Triangle


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- VW.intersectsLine UX ∧ X.onLine VW
-- To:
-- twoLinesIntersectAtPoint UX VW X
