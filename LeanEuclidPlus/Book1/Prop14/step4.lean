import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_14_step4 (a b c d e : Point)
  (h2 : ∠ a:b:c + ∠ a:b:e = ∟ + ∟)
  (h3 : ∠ a:b:c + ∠ a:b:d = ∟ + ∟)
  : ∠ c:b:a + ∠ a:b:e = ∠ c:b:a + ∠ a:b:d := by
  euclid_finish

end Elements.Book1
