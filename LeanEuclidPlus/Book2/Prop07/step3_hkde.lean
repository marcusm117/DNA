import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.7.3 sub: HF ∥ DE. HF ∥ AB and DE ∥ AB, so HF ∥ DE by transitivity [Prop.~1.30]. The three
   lines are pairwise distinct (hypotheses). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_hkde (HF DE AB : Line)
    (hHFDE : HF ≠ DE) (hDEAB : DE ≠ AB) (hABHF : AB ≠ HF)
    (hHFAB : ¬(HF.intersectsLine AB)) (hDEAB' : ¬(DE.intersectsLine AB)) :
    ¬(HF.intersectsLine DE) := by
  euclid_intros
  euclid_apply (proposition_30 HF DE AB)
  euclid_finish

end Elements.Book2
