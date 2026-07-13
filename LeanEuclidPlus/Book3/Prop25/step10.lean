import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step10 (a c d e : Point)
    (hassump1 : |(a─d)| = |(d─c)|)
    (hassump2 : |(d─e)| = |(d─e)|) :
    |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)| := by
  euclid_finish

end Elements.Book3
