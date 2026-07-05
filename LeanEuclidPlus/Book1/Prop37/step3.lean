import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_37_step3 (c f : Point) (BD CF : Line)
    (h_c_CF : c.onLine CF) (h_f_CF : f.onLine CF) (h_CF_BD : ¬CF.intersectsLine BD) :
    c.onLine CF ∧ f.onLine CF ∧ ¬CF.intersectsLine BD :=
  ⟨h_c_CF, h_f_CF, h_CF_BD⟩

end Elements.Book1
