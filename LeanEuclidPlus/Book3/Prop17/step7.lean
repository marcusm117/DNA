import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step7
    (a e f : Point) (BCD AFG : Circle)
    (ha_onAFG : a.onCircle AFG)
    (hf_onAFG : f.onCircle AFG)
    (hassump1 : e.isCentre BCD ∧ e.isCentre AFG) :
    |(e─a)| = |(e─f)| := by
  have h := point_on_circle_onlyif e a f AFG ⟨hassump1.2, ha_onAFG, hf_onAFG⟩
  linarith [segment_symmetric e a, segment_symmetric e f]

end Elements.Book3
