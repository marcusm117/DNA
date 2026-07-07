import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step2 (f c : Point) (FC : Line)
    (hfFC : f.onLine FC) (hcFC : c.onLine FC)
    : f.onLine FC ∧ c.onLine FC := ⟨hfFC, hcFC⟩

end Elements.Book3
