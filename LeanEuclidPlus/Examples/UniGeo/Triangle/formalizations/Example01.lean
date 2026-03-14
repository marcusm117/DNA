import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Triangle

theorem theorem_1 : ∀ (U V W X : Point) (UV VW WU UX : Line),
  formTriangle U V W UV VW WU ∧
  distinctPointsOnLine U X UX ∧
  twoLinesIntersectAtPoint UX VW X ∧
  between V X W ∧
  ∠ W:U:X = ∠ V:U:X ∧
  ∠ V:X:U = ∟ →
  |(W─X)| = |(V─X)| :=
by
  euclid_intros
  have : ∠ U:X:V = ∠ U:X:W := by euclid_finish
  have : △U:V:X≅△U:W:X := by euclid_finish
  have : |(W─X)| = |(V─X)| := by
    -- euclid_apply (△U:V:X).congruent_if △U:W:X
    euclid_finish
  euclid_finish

end UniGeo.Triangle