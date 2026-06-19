import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- EF ≠ AB: g∈EF. If EF=AB then g∈AB, giving EF∩AB — contradicts ¬(EF∥AB). -/
theorem helper_2_5_step7_dfpar_efne (g : Point) (AB EF : Line)
    (hgEF : g.onLine EF)
    (hEFAB : ¬(EF.intersectsLine AB)) :
    EF ≠ AB := by
  euclid_intros
  rename_i heq
  have hgAB : g.onLine AB := heq ▸ hgEF
  have hint : EF.intersectsLine AB := by
    euclid_apply (intersection_lines_common_point g EF AB)
    euclid_finish
  exact hEFAB hint

end Elements.Book2
