import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step4 (a b d : Point) (AD BE : Line)
    (hb_on : b.onLine BE) (hpar : ¬(BE.intersectsLine AD)) :
    b.onLine BE ∧ ¬(BE.intersectsLine AD) :=
  ⟨hb_on, hpar⟩

end Elements.Book1
