import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_32_step9 (a' b d f : Point)
    (step7 : ∠ b:a':d + ∠ a':b:d = ∟) (step8 : ∠ a':b:f = ∟) :
    ∠ a':b:f = ∠ b:a':d + ∠ a':b:d := by
  euclid_finish

end Elements.Book3
