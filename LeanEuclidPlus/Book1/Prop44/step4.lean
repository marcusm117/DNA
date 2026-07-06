import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_44_step4
    (h : Point) (AH BG : Line)
    (hhAH : h.onLine AH)
    (hpar : ¬(AH.intersectsLine BG))
    : h.onLine AH ∧ ¬(AH.intersectsLine BG) :=
  ⟨hhAH, hpar⟩

end Elements.Book1
