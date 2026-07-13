import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- e0 is off AB: if e0 were on AB then a, e0, b collinear, so ∠e0:a:b = 0 (not between) or 2∟
-- (between e0 a b) — both contradict ∠e0:a:b = ∟ (with ∟ > 0).  (a ≠ e0 since e0 is off AD.)
theorem helper_3_33_hFG_int_AE_he0_offAB
    (a b c₁ c c₂ e0 : Point) (AD AB : Line)
    (haad : a.onLine AD) (he0off : ¬ e0.onLine AD)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (heq : ∠ e0:a:b = ∟) :
    ¬ e0.onLine AB := by
  intro he0AB
  by_cases hbet : between e0 a b
  · euclid_apply (flat_angle_onlyif e0 a b)
    linarith [right_angle_pos]
  · euclid_apply (degenerated_angle_if a e0 b AB)
    linarith [right_angle_pos]

end Elements.Book3
