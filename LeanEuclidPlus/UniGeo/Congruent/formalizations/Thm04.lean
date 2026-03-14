import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_4 : ∀ (U V W X Y : Point) (UV VX UX VW WY VY UW : Line),
  formTriangle U V X UV VX UX ∧
  formTriangle V W Y VW WY VY ∧
  between U V W ∧
  distinctPointsOnLine U W UW ∧
  X.sameSide Y UW ∧ X ≠ Y ∧
  ∠ V:Y:W = ∠ U:X:V ∧
  |(U─X)| = |(V─Y)| ∧
  ¬ UX.intersectsLine VY →
  (△ V:W:Y).congruent (△ U:V:X) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29'''' Y X W V U VY UX UW
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle U V X UW VX UX ∧
-- formTriangle V W Y UW WY VY ∧
-- X.sameSide Y UW ∧
-- To:
-- formTriangle U V X UV VX UX ∧
-- formTriangle V W Y VW WY VY ∧
-- distinctPointsOnLine U W UW ∧
-- X.sameSide Y UW ∧ X ≠ Y
