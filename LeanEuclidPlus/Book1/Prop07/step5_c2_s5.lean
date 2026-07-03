import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- ∠d:c:b = ∠a:d:c + ∠a:c:b from sumc (angle sum at C) + step4 (angle symmetry ∠d:c:a = ∠a:c:d = ∠a:d:c)
theorem helper_1_7_step5_c2_s5 (a b c d : Point) (AC CB AD CD : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hcCB : c.onLine CB) (hbCB : b.onLine CB) (hcb : c ≠ b)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (had : a ≠ d)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hcd : c ≠ d)
    (step4 : ∠ a:c:d = ∠ a:d:c)
    (step5_c2_sumc : ∠ d:c:b = ∠ d:c:a + ∠ a:c:b)
    : ∠ d:c:b = ∠ a:d:c + ∠ a:c:b := by
  have h_sym : ∠ d:c:a = ∠ a:c:d := by euclid_finish
  linarith

end Elements.Book1
