import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.7.3 sub: CN ∥ BE. CN ∥ AD (vertical through c parallel to the left side AD) and AD ∥ BE
   (the square's two opposite sides), so CN ∥ BE by transitivity [Prop.~1.30]. The three lines are
   pairwise distinct (hypotheses). -/
theorem helper_2_7_step3_cfbe (a : Point) (CN AD BE : Line)
    (haAD : a.onLine AD) (step3_anbe : ¬(a.onLine BE))
    (hCNBE : CN ≠ BE) (hADCN : AD ≠ CN)
    (hCNAD : ¬(CN.intersectsLine AD)) (hADBE : ¬(AD.intersectsLine BE)) :
    ¬(CN.intersectsLine BE) := by
  euclid_intros
  have hADBEne : AD ≠ BE := fun hh => step3_anbe (hh ▸ haAD)
  have hBEAD : BE ≠ AD := fun hh => hADBEne hh.symm
  euclid_apply (proposition_30 CN BE AD)
  euclid_finish

end Elements.Book2
