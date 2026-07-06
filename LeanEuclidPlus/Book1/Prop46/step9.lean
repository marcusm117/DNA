import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step9
    (a b d e : Point)
    (step2 : |(a─d)| = |(a─b)|)
    (step6 : |(a─b)| = |(d─e)|)
    (step7 : |(a─d)| = |(b─e)|) :
    |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)| := by
  refine ⟨?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book1
