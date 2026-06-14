import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.9 sub: CF ∥ BE. CF ∥ AD (vertical through c parallel to the left side AD) and AD ∥ BE
   (the square's two opposite sides), so CF ∥ BE by transitivity [Prop.~1.30]. The three lines are
   pairwise distinct (taken as hypotheses, established from the figure's off-line points). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step9_cfbe (CF AD BE : Line)
    (hCFBE : CF ≠ BE) (hBEAD : BE ≠ AD) (hADCF : AD ≠ CF)
    (hCFAD : ¬(CF.intersectsLine AD)) (hADBE : ¬(AD.intersectsLine BE)) :
    ¬(CF.intersectsLine BE) := by
  euclid_intros
  euclid_apply (proposition_30 CF BE AD)
  euclid_finish

end Elements.Book2
