import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_18 : ∀ (V X Y W Z : Point) (VX VY WZ XY : Line),
  formTriangle V X Y VX XY VY ∧
  distinctPointsOnLine W Z WZ ∧
  twoLinesIntersectAtPoint WZ VY Z ∧
  twoLinesIntersectAtPoint WZ VX W ∧
  between V W X ∧
  between V Z Y ∧
  ¬ XY.intersectsLine WZ ∧
  ∠ V:Y:X = ∠ W:X:Y →
  ∠ V:W:Z = ∠ V:Z:W :=
by
  euclid_intros
  have : ∠ V:Y:X = ∠ V:Z:W := by
    euclid_apply Elements.Book1.proposition_29'''' W X V Z Y WZ XY VY
    euclid_finish
  have : ∠ W:X:Y = ∠ V:W:Z := by
    euclid_apply Elements.Book1.proposition_29'''' Z Y V W X WZ XY VX
    euclid_finish
  euclid_finish

end UniGeo.Parallel


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- distinctPointsOnLine V X VX ∧
-- distinctPointsOnLine V Y VY ∧
-- distinctPointsOnLine X Y XY ∧
-- VX.intersectsLine WZ ∧ W.onLine VX ∧
-- VY.intersectsLine WZ ∧ Z.onLine VY ∧
-- VX.intersectsLine XY ∧
-- VY.intersectsLine XY ∧
-- To:
-- formTriangle V X Y VX XY VY ∧
-- distinctPointsOnLine W Z WZ ∧
-- twoLinesIntersectAtPoint WZ VY Z ∧
-- twoLinesIntersectAtPoint WZ VX W ∧
