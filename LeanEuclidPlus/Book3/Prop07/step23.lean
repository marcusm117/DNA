import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step23
    (ABCD : Circle) (f g k : Point)
    (hk_on : k.onCircle ABCD)
    (hk_eq : |(f─k)| = |(f─g)|)
    : k.onCircle ABCD ∧ |(f─k)| = |(f─g)| :=
  ⟨hk_on, hk_eq⟩

end Elements.Book3
