import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- TODO: fill object/hypothesis binders (run --context step7)
theorem helper_1_9_step7 (a d e f : Point)
    (hassump1 : |(a─d)| = |(a─e)|)
    (hassump2 : |(a─f)| = |(a─f)|) :
    |(d─a)| = |(e─a)| ∧ |(a─f)| = |(a─f)| :=
  ⟨by euclid_finish, hassump2⟩

end Elements.Book1
