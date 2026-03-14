import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_13 : ∀ (Q S T R U : Point) (SQ TQ ST RU : Line),
  formTriangle Q S T SQ ST TQ ∧
  distinctPointsOnLine R U RU ∧
  twoLinesIntersectAtPoint RU SQ R ∧
  twoLinesIntersectAtPoint RU TQ U ∧
  between Q R S ∧
  between Q U T ∧
  ∠ Q:R:U = ∠ Q:U:R ∧
  ¬ ST.intersectsLine RU →
  ∠ R:S:T = ∠ S:T:Q :=
by
  euclid_intros
  have : ∠ U:T:S = ∠ Q:U:R := by
    euclid_apply Elements.Book1.proposition_29'''' R S Q U T RU ST TQ
    euclid_finish
  have : ∠ R:S:T = ∠ Q:R:U := by
    euclid_apply Elements.Book1.proposition_29'''' U T Q R S RU ST SQ
    euclid_finish
  euclid_finish

end UniGeo.Parallel


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- distinctPointsOnLine Q S QS ∧
-- distinctPointsOnLine Q T QT ∧
-- distinctPointsOnLine S T ST ∧
-- distinctPointsOnLine R U RU ∧
-- QS.intersectsLine RU ∧ R.onLine QS ∧
-- QT.intersectsLine RU ∧ U.onLine QT ∧
-- QS.intersectsLine ST ∧
-- QT.intersectsLine ST ∧
-- To:
-- formTriangle Q S T SQ ST TQ ∧
-- distinctPointsOnLine R U RU ∧
-- twoLinesIntersectAtPoint RU SQ R ∧
-- twoLinesIntersectAtPoint RU TQ U ∧
