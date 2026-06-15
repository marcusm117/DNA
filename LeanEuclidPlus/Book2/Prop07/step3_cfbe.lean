import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.7.3 sub: CN ∥ BE. CN ∥ AD (vertical through c parallel to the left side AD) and AD ∥ BE
   (the square's two opposite sides), so CN ∥ BE by transitivity [Prop.~1.30]. The three lines are
   pairwise distinct (hypotheses). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_cfbe (CN AD BE : Line)
    (hCNBE : CN ≠ BE) (hBEAD : BE ≠ AD) (hADCN : AD ≠ CN)
    (hCNAD : ¬(CN.intersectsLine AD)) (hADBE : ¬(AD.intersectsLine BE)) :
    ¬(CN.intersectsLine BE) := by
  euclid_intros
  euclid_apply (proposition_30 CN BE AD)
  euclid_finish

end Elements.Book2
