import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_2 : ∀ (A B C D E F G H P : Point) (AB CD EF GH AH GB AG HB : Line),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine E F EF ∧
  distinctPointsOnLine G H GH ∧
  P.onLine AB ∧
  P.onLine CD ∧
  P.onLine EF ∧
  P.onLine GH ∧
  E.opposingSides C GH ∧
  E.opposingSides B GH ∧
  E.opposingSides F GH ∧
  A.opposingSides C GH ∧
  A.opposingSides B GH ∧
  A.opposingSides F GH ∧
  D.opposingSides C GH ∧
  D.opposingSides B GH ∧
  D.opposingSides F GH ∧
  between G P H ∧
  |(G─P)| = |(P─H)| ∧
  ∠ G:A:B = ∠ G:B:A ∧
  ∠ G:B:A = ∠ H:A:B ∧
  |(H─A)| = |(H─B)| →
  formConvexQuadrilateral A H G B AH GB AG HB ∧
  |(A─H)| = |(H─B)| ∧
  |(H─B)| = |(B─G)| ∧
  |(B─G)| = |(G─A)| :=
by sorry

end UniGeo.Additional
