import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.7.3 sub: DE ∥ HF. DE ∥ AB (the square's bottom side parallel to the base) and HF ∥ AB, so
   DE ∥ HF by transitivity [Prop.~1.30]. The three lines are pairwise distinct (hypotheses). -/
theorem helper_2_7_step3_dehf (DE HF AB : Line)
    (hDEHF : DE ≠ HF) (hHFAB : HF ≠ AB) (hABDE : AB ≠ DE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hHFAB' : ¬(HF.intersectsLine AB)) :
    ¬(DE.intersectsLine HF) := by
  euclid_intros
  euclid_apply (proposition_30 DE HF AB)
  euclid_finish

end Elements.Book2
