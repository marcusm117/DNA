import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_23_step4 (a b c d : Point)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ a:c:b = ∠ a:d:b)   -- "segment $ACB$ is similar to segment $ADB$"
  : ∠ a:c:b = ∠ a:d:b := by
  exact hassump1

end Elements.Book3
