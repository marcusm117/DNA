import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step2 (c d : Point) (EFG : Circle)
    (hcen : c.isCentre EFG) (hdon : d.onCircle EFG) :
    c.isCentre EFG ∧ d.onCircle EFG :=
  ⟨hcen, hdon⟩

end Elements.Book1
