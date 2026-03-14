import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_16 : ∀ (T V W U X : Point) (TV TW XU VW : Line),
  formTriangle T V W TV VW TW ∧
  distinctPointsOnLine X U XU ∧
  twoLinesIntersectAtPoint XU TV U ∧
  twoLinesIntersectAtPoint XU TW X ∧
  between T U V ∧
  between T X W ∧
  ∠ T:U:X = ∠ T:W:V ∧
  ¬ XU.intersectsLine VW →
  ∠ U:V:W = ∠ T:W:V :=
by
  euclid_intros
  have : ∠ U:V:W = ∠ T:U:X := by
    euclid_apply Elements.Book1.proposition_29'''' X W T U V XU VW TV
    euclid_finish
  euclid_finish

end UniGeo.Parallel


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- distinctPointsOnLine T V TV ∧
-- distinctPointsOnLine T W TW ∧
-- distinctPointsOnLine U X UX ∧
-- distinctPointsOnLine V W VW ∧
-- TV.intersectsLine UX ∧ U.onLine TV ∧
-- TW.intersectsLine UX ∧ X.onLine TW ∧
-- TV.intersectsLine VW ∧
-- TW.intersectsLine VW ∧
-- To:
-- formTriangle T V W TV VW TW ∧
-- distinctPointsOnLine U X XU ∧
-- twoLinesIntersectAtPoint XU TV U ∧
-- twoLinesIntersectAtPoint XU TW X ∧
