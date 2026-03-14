import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_5 : ∀ (E F G H : Point) (EF FG GE EH : Line),
  formTriangle E F G EF FG GE ∧
  distinctPointsOnLine E H EH ∧
  twoLinesIntersectAtPoint EH FG H ∧
  between F H G ∧
  ∠ H:E:F = ∠ H:E:G ∧
  |(E─G)| = |(E─F)| →
  |(G─H)| = |(F─H)| :=
by
  euclid_intros
  euclid_assert (△ E:F:H).congruent (△ E:G:H)
  euclid_finish

end UniGeo.Triangle


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- FG.intersectsLine EH ∧ H.onLine FG
-- To:
-- twoLinesIntersectAtPoint EH FG H
