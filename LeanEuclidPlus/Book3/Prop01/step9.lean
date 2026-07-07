import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step9 (a b d g : Point)
    (hassump1 : |(a─d)| = |(d─b)|)
    (hassump2 : |(d─g)| = |(d─g)|) :
    |(a─d)| = |(b─d)| ∧ |(d─g)| = |(d─g)| :=
  ⟨by euclid_finish, rfl⟩

end Elements.Book3
