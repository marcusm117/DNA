import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_32_step4
    (a b c e : Point) (AB BC AC CE : Line)
    (hstep2 : ∠ b:a:c = ∠ a:c:e) :
    ∠ a:c:e = ∠ b:a:c := by
  exact hstep2.symm

end Elements.Book1
