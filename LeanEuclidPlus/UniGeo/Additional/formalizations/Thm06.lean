import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_6 : ∀ (A B C D E F G : Point) (AE FG : Line),
  distinctPointsOnLine A E AE ∧
  B.onLine AE ∧ C.onLine AE ∧ D.onLine AE ∧
  between A B C ∧ between B C D ∧ between C D E ∧
  |(A─C)| = |(C─E)| ∧
  |(B─C)| = |(C─D)| ∧
  distinctPointsOnLine F G FG ∧
  twoLinesIntersectAtPoint FG AE C ∧
  F.opposingSides G AE ∧
  ∠ F:C:A = ∟ ∧
  |(A─F)| = |(E─F)| →
  (△ A:B:F).congruent (△ E:D:F) :=
by sorry

end UniGeo.Additional
