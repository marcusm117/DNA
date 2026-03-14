import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_10 : ∀ (V Y W X Z : Point) (VY YZ VZ WX XZ WZ WY XV : Line),
  formTriangle V Y Z VY YZ VZ ∧
  formTriangle W X Z WX XZ WZ ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine X V XV ∧
  twoLinesIntersectAtPoint WY XV Z ∧
  between W Z Y ∧
  between X Z V ∧
  ¬ WX.intersectsLine VY ∧
  ∠ Y:V:Z = ∠ Z:Y:V →
  ∠ X:W:Z = ∠ W:X:Z :=
by
  euclid_intros
  have : ∠ Y:V:Z= ∠ W:X:Z := by
    euclid_apply Elements.Book1.proposition_29''' W Y X V WX VY XV
    euclid_finish
  have : ∠ X:W:Z = ∠ V:Y:Z := by
    euclid_apply Elements.Book1.proposition_29''' V X Y W VY WX WY
    euclid_finish
  euclid_finish

end UniGeo.Parallel


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- distinctPointsOnLine V Y VY ∧
-- distinctPointsOnLine W X WX ∧
-- distinctPointsOnLine W Y WY ∧
-- distinctPointsOnLine V X VX ∧
-- To:
-- formTriangle V Y Z VY YZ VY ∧
-- formTriangle W X Z WX XZ WZ ∧
-- distinctPointsOnLine W Y WY ∧
--  distinctPointsOnLine X V XV ∧
