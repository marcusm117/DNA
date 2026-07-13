import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step18 (a c f : Point)
    (hstep17 : |(a─f)| = |(f─c)|) : |(a─f)| = |(f─c)| := hstep17

end Elements.Book3
