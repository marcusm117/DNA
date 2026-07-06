import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step2
    (a : Point) (AL BD CE : Line)
    (ha_AL : a.onLine AL) (h_nALBD : ¬AL.intersectsLine BD) :
    a.onLine AL ∧ (¬(AL.intersectsLine BD) ∨ ¬(AL.intersectsLine CE)) := by
  exact ⟨ha_AL, Or.inl h_nALBD⟩

end Elements.Book1
