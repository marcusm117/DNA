import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_32_step1 (c e : Point) (AB CE : Line)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE) (hCE_AB : ¬CE.intersectsLine AB) :
    c.onLine CE ∧ e.onLine CE ∧ ¬(CE.intersectsLine AB) := by
  exact ⟨hc_CE, he_CE, hCE_AB⟩

end Elements.Book1
