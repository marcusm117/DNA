import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- b is off AD: if b were on AD then a, b, d collinear, so ∠d:a:b = 0 (not between) or 2∟
-- (between d a b) — both contradict 0 < ∠d:a:b < ∟.  Proven explicitly (euclid_finish loops on
-- the opaque-angle → off-line inference).
theorem helper_3_33_hFG_int_AE_hb_offAD
    (a b c₁ c c₂ d : Point) (AD : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hne : a ≠ b) (hadd : d ≠ a)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟) :
    ¬ b.onLine AD := by
  intro hbAD
  by_cases hbet : between d a b
  · euclid_apply (flat_angle_onlyif d a b)
    linarith [right_angle_pos]
  · euclid_apply (degenerated_angle_if a d b AD)
    linarith

end Elements.Book3
