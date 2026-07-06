import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step5 (c : Point) (CG EF : Line)
    (h_c_CG : c.onLine CG) (h_par : ¬CG.intersectsLine EF) :
    c.onLine CG ∧ ¬CG.intersectsLine EF :=
  ⟨h_c_CG, h_par⟩

end Elements.Book1
