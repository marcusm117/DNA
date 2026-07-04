import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_16_step11 (a b c e f : Point)
    (h_step10 : (∠ b:a:e = ∠ e:c:f) ∧ (∠ a:b:e = ∠ c:f:e)) :
    ∠ b:a:e = ∠ e:c:f :=
  h_step10.1

end Elements.Book1
