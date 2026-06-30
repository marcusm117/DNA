import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step2
    (a e c : Point)
    (hbet : between a e c) (hlen : |(a─e)| = |(e─c)|) :
    between a e c ∧ |(a─e)| = |(e─c)| := by
  exact ⟨hbet, hlen⟩

end Elements.Book2
