import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.15 sub: DE ∥ HK. DE ∥ AB (the square's bottom side parallel to the base) and HK ∥ AB, so
   DE ∥ HK by transitivity [Prop.~1.30]. The three lines are pairwise distinct (hypotheses). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step15_dehk (DE HK AB : Line)
    (hDEHK : DE ≠ HK) (hHKAB : HK ≠ AB) (hABDE : AB ≠ DE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hHKAB' : ¬(HK.intersectsLine AB)) :
    ¬(DE.intersectsLine HK) := by
  euclid_intros
  euclid_apply (proposition_30 DE HK AB)
  euclid_finish

end Elements.Book2
