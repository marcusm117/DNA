import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_15 : ∀ (V W X Y Z : Point) (VY YZ VZ WX XZ WZ XY VW : Line),
  formTriangle V Y Z VY YZ VZ ∧
  formTriangle W X Z WX XZ WZ ∧
  distinctPointsOnLine X Y XY ∧
  distinctPointsOnLine V W VW ∧
  twoLinesIntersectAtPoint XY VW Z ∧
  between V Z W ∧
  between X Z Y ∧
  ∠ X:W:Z = ∠ V:Y:Z →
  (△ W:X:Z).similar (△ Y:V:Z) :=
by
  euclid_intros
  have : ∠ V:Z:Y = ∠ W:Z:X := by
    euclid_apply Elements.Book1.proposition_15 V W X Y Z VW XY
    euclid_finish
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle V Y Z VY XY VW ∧
-- formTriangle W X Z WX XY VW ∧
-- To:
-- formTriangle V Y Z VY YZ VZ ∧
-- formTriangle W X Z WX XZ WZ ∧
-- distinctPointsOnLine X Y XY ∧
-- distinctPointsOnLine V W VW ∧
-- twoLinesIntersectAtPoint XY VW Z ∧
