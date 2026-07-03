import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step18 (b c f g : Point)
    (h_step17 : (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c)) :
    ∠ f:b:c = ∠ g:c:b := h_step17.1

end Elements.Book1
