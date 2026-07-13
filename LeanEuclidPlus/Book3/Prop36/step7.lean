import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step7 (a b c d f : Point)
    (hstep5 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)|)
    (hstep6 : |(f─c)| = |(f─b)|) :
    |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─d)| * |(f─d)| := by
  rw [hstep6] at hstep5; exact hstep5

end Elements.Book3
