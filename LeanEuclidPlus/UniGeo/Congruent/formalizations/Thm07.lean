import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_7 : ∀ (W X Y Z : Point) (WX YZ WZ XY WY : Line),
  formConvexQuadrilateral W X Z Y WX YZ WZ XY ∧
  distinctPointsOnLine W Y WY ∧
  |(W─X)| = |(Y─Z)| ∧
  ¬ WX.intersectsLine YZ →
  (△ W:Y:Z).congruent (△ Y:W:X) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29''' X Z W Y WX YZ WY
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle W X Y WX XY WY ∧
-- formTriangle W Y Z WY YZ WZ ∧
-- X.opposingSides Z WY ∧
-- To:
-- formConvexQuadrilateral W X Z Y WX YZ WZ XY ∧
-- distinctPointsOnLine W Y WY ∧
