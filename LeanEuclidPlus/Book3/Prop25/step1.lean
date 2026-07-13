import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step1 (a c d : Point)
    (hbet : between a d c) (hlen : |(a─d)| = |(d─c)|) :
    between a d c ∧ |(a─d)| = |(d─c)| := by
  exact ⟨hbet, hlen⟩

end Elements.Book3
