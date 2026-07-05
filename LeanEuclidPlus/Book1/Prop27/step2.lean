import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step2
  (g b : Point) (AE FD EF : Line)
  (h_g_AE : g.onLine AE) (h_g_FD : g.onLine FD) (hbd : g.sameSide b EF)
  : g.onLine AE ∧ g.onLine FD ∧ g.sameSide b EF :=
  ⟨h_g_AE, h_g_FD, hbd⟩

end Elements.Book1
