import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.22 sub: HK ∥ DE. HK ∥ AB and DE ∥ AB, so HK ∥ DE by transitivity [Prop.~1.30]. The three
   lines are pairwise distinct (hypotheses, from off-line points). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step22_hkde (HK DE AB : Line)
    (hHKDE : HK ≠ DE) (hDEAB : DE ≠ AB) (hABHK : AB ≠ HK)
    (hHKAB : ¬(HK.intersectsLine AB)) (hDEAB' : ¬(DE.intersectsLine AB)) :
    ¬(HK.intersectsLine DE) := by
  euclid_intros
  euclid_apply (proposition_30 HK DE AB)
  euclid_finish

end Elements.Book2
