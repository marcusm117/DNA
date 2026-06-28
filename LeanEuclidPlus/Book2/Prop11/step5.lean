import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_11_step5
    (e f f0 b : Point)
    (hbet : between e f f0) (hlen : |(e─f)| = |(b─e)|) :
    between e f f0 ∧ |(e─f)| = |(b─e)| := by
  exact ⟨hbet, hlen⟩

end Elements.Book2
