import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_7_step3 (c d : Point) (CD : Line)
    (hc : c.onLine CD) (hd : d.onLine CD) : c.onLine CD ∧ d.onLine CD :=
  ⟨hc, hd⟩

end Elements.Book1
