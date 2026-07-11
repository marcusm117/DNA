import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step11_assumption2_tri_efg
    (e f g : Point) (ABCD : Circle)
    (FE FG EG : Line)
    (h_centre : e.isCentre ABCD)
    (hf_on : f.onCircle ABCD) (hg_on : g.onCircle ABCD)
    (hf_FE : f.onLine FE) (he_FE : e.onLine FE)
    (he_EG : e.onLine EG) (hg_EG : g.onLine EG)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hfg : f ≠ g) :
    formTriangle e f g FE FG EG := by
  euclid_finish

end Elements.Book3
