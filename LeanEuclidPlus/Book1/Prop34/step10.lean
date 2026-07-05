import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_34_step10
  (a b c d : Point) (AB CD AC BD BC : Line)
  (hstep5 : |(a─b)| = |(c─d)|)
  (hstep6 : |(a─c)| = |(b─d)|)
  (hstep8 : ∠ a:b:d = ∠ a:c:d)
  (hstep7 : ∠ b:a:c = ∠ c:d:b)
  : |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c = ∠ c:d:b :=
  ⟨hstep5, hstep6, hstep8, hstep7⟩

end Elements.Book1
