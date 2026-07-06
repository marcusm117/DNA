import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step1 (b e c : Point)
    (hbet : between b e c) (heq : |(b─e)| = |(e─c)|) :
    between b e c ∧ |(b─e)| = |(e─c)| :=
  ⟨hbet, heq⟩

end Elements.Book1
