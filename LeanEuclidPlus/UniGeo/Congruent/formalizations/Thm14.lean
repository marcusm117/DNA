import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_14 : ∀ (U V W X Y : Point) (UX XY UY VW WY VY UW VX : Line),
  formTriangle U X Y UX XY UY ∧
  formTriangle V W Y VW WY VY ∧
  distinctPointsOnLine U W UW ∧
  distinctPointsOnLine V X VX ∧
  between U Y W ∧
  between V Y X ∧
  |(U─Y)| = |(W─Y)| ∧
  |(U─X)| = |(V─W)| ∧
  |(X─Y)| = |(V─Y)| →
  ∠ V:W:Y = ∠ X:U:Y :=
by
  euclid_intros
  euclid_assert (△ U:X:Y).congruent (△ W:V:Y)
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle Q T U QT RT QS ∧
-- formTriangle R S U RS QS RT ∧
-- To:
-- formTriangle U X Y UX XY UY ∧
-- formTriangle V W Y VW WY VY ∧
-- distinctPointsOnLine U W UW ∧
-- distinctPointsOnLine V X VX ∧
