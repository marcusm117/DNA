import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_32_step14 (a b c d e f : Point)
  (hassump1 : ∠ f:b:d = ∠ b:a:d)   -- "$BAD$ was shown (to be) equal to $DBF$"
  (step12 : ∠ b:a:d + ∠ b:c:d = ∟ + ∟) (step13 : ∠ f:b:d + ∠ e:b:d = ∟ + ∟) :
  ∠ f:b:d + ∠ e:b:d = ∠ b:a:d + ∠ b:c:d := by
  euclid_finish

end Elements.Book3
