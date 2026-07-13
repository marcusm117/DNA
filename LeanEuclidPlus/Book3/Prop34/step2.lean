import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_34_step2 (b c f d1 d d2 : Point)
    (hangle_fbc : ∠ f:b:c = ∠ d1:d:d2) :
    ∠ f:b:c = ∠ d1:d:d2 := hangle_fbc

end Elements.Book3
