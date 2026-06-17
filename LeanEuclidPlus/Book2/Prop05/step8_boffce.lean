import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(b.onLine CE). b,c on AB with b ≠ c; c on CE. If b ∈ CE then AB = CE
   (two points b,c determine the line), so e ∈ CE = AB — but e is off AB (e on EF ∥ AB).
   Mirror of the proven step11_aoffCE template (end on a term, not euclid_finish). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_boffce (a b c d e : Point) (AB CE EF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (heEF : e.onLine EF)
    (hacd : between a c d) (hcdb : between c d b)
    (heoffAB : ¬(e.onLine AB)) :
    ¬(b.onLine CE) := by
  intro hbCE
  have hbc : b ≠ c := by euclid_finish
  have hABisCE : AB = CE := by
    euclid_apply (two_points_determine_line b c AB CE)
    euclid_finish
  exact heoffAB (hABisCE ▸ heCE)

end Elements.Book2
