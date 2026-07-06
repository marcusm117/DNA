import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step6_par (EF CG : Line)
    (h_par_CG_EF : ¬CG.intersectsLine EF) :
    ¬EF.intersectsLine CG :=
  fun h => h_par_CG_EF (intersection_symm EF CG h)

end Elements.Book1
