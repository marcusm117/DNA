import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_8_step1 (ABC : Circle) (m m' : Point)
    (hm : m.isCentre ABC) (hm' : m'.isCentre ABC) :
    m'.isCentre ABC ∧ m' = m :=
  ⟨hm', centre_unique m' m ABC ⟨hm', hm⟩⟩

end Elements.Book3
