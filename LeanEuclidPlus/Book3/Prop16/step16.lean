import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- |d─a| = |d─h| since both a and h are on circle ABC centered at d.
theorem helper_3_16_step16
    (a h d : Point) (ABC : Circle)
    (left : d.isCentre ABC)
    (left_1 : a.onCircle ABC)
    (hhcircle : h.onCircle ABC)
    : |(d─a)| = |(d─h)| := by
  have h1 := point_on_circle_onlyif d a h ABC ⟨left, left_1, hhcircle⟩
  linarith [segment_symmetric d a, segment_symmetric d h]

end Elements.Book3
