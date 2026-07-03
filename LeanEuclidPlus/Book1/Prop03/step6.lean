import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_3_step6 (a d e c₀ c₁ : Point)
    (hstep3 : |(a─e)| = |(a─d)|) (hstep4 : |(c₀─c₁)| = |(a─d)|) :
    |(a─e)| = |(c₀─c₁)| := by
  exact hstep3.trans hstep4.symm

end Elements.Book1
