import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_32_step6
    (a b c d : Point) (AB BC AC : Line)
    (hstep5 : ∠ a:c:d = ∠ b:a:c + ∠ a:b:c) :
    ∠ a:c:d + ∠ a:c:b = ∠ b:a:c + ∠ a:b:c + ∠ a:c:b := by
  euclid_finish

end Elements.Book1
