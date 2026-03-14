import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_14 : ∀ (V W X Y Z : Point) (XW WY XY VW WZ VZ XZ VY : Line),
  formTriangle X W Y XW WY XY ∧
  formTriangle V W Z VW WZ VZ ∧
  distinctPointsOnLine X Z XZ ∧
  distinctPointsOnLine V Y VY ∧
  twoLinesIntersectAtPoint XZ VY W ∧
  between V W Y ∧
  between X W Z ∧
  |(W─Z)| / |(W─X)| = |(V─W)| / |(W─Y)| →
  (△ V:W:Z).similar (△ Y:W:X) :=
by
  euclid_intros
  have : ∠ X:W:Y = ∠ V:W:Z := by
    euclid_apply Elements.Book1.proposition_15 X Z V Y W XZ VY
    euclid_finish
  apply Triangle.similar_sas (△ V:W:Z) (△ Y:W:X)
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle V W Z VY XZ VZ ∧
-- formTriangle W X Y XZ XY VY ∧
-- To:
-- formTriangle X W Y XW WY XY ∧
-- formTriangle V W Z VW WZ VZ ∧
-- distinctPointsOnLine X Z XZ ∧
-- distinctPointsOnLine V Y VY ∧
-- twoLinesIntersectAtPoint XZ VY W ∧
