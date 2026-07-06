import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step10
    (k : Point) (HB EF : Line)
    (hkHB : k.onLine HB)
    (hkEF : k.onLine EF)
    : k.onLine HB ∧ k.onLine EF :=
  ⟨hkHB, hkEF⟩

end Elements.Book1
