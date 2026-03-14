import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_9 : ∀ (U V W X Y : Point) (UX XY UY VW WY VY WU VX : Line),
  formTriangle V W Y VW WY VY ∧
  formTriangle U X Y UX XY UY ∧
  distinctPointsOnLine W U WU ∧
  distinctPointsOnLine V X VX ∧
  twoLinesIntersectAtPoint WU VX Y ∧
  between V Y X ∧
  ∠ V:W:Y = ∠ X:U:Y ∧
  between U Y W ∧
  |(W─Y)| = |(U─Y)| →
  (△ V:W:Y).congruent (△ X:U:Y) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_15 U W X V Y WU VX
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle U X Y UX VX UW ∧
-- formTriangle V W Y VW UW VX ∧
-- To:
-- formTriangle U X Y UX XY UY ∧
-- formTriangle V W Y VW WY VY ∧
-- distinctPointsOnLine W U WU ∧
-- distinctPointsOnLine V X VX ∧
-- twoLinesIntersectAtPoint WU VX Y ∧
