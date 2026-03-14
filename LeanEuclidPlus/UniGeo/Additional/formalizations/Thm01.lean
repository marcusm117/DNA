import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_1 : ∀ (A B C D E F G : Point) (AB BC DC DE EA AC AD BE : Line),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine C D DC ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine E A EA ∧
  A.sameSide B DE ∧ B.sameSide C DE ∧
  B.sameSide C EA ∧ C.sameSide D EA ∧
  C.sameSide D AB ∧ D.sameSide E AB ∧
  D.sameSide E BC ∧ E.sameSide A BC ∧
  E.sameSide A DC ∧ A.sameSide B DC ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine B E BE ∧
  twoLinesIntersectAtPoint AC BE F ∧
  twoLinesIntersectAtPoint AD BE G ∧
  between E G F ∧
  |(E─G)| = |(G─F)| ∧
  between G F B ∧
  |(G─F)| = |(F─B)| ∧
  ∠ B:A:C = ∠ E:A:D ∧
  |(A─B)| = |(A─E)| →
  (△ A:B:F).congruent (△ A:E:G) :=
by sorry

end UniGeo.Additional
