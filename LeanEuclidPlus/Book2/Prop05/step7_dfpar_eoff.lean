import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- e∉AB: e∈EF, ¬(EF∥AB). After euclid_intros (goal=False, a✝:e.onLine AB in ctx),
   build EF.intersectsLine AB via separate have, then exact contradiction. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_eoff (e : Point) (AB EF : Line)
    (heEF : e.onLine EF)
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ¬(e.onLine AB) := by
  euclid_intros
  have hEFAB2 : EF.intersectsLine AB := by
    euclid_apply (intersection_lines_common_point e EF AB)
    euclid_finish
  exact hEFAB hEFAB2

end Elements.Book2
