import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- b∉DG. b∈AB, d∈AB∩DG, between c d b → d≠b.
   Sub-node abdg: AB=DG. Sub-node dgce_ne: DG≠CE.
   Then c∈AB=DG, c∈CE, DG≠CE → DG∩CE → hDGCE contradiction. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_boffDG (b c d : Point) (AB CE DG : Line)
    (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hdDG : d.onLine DG) (hcCE : c.onLine CE)
    (hDGCE : ¬(DG.intersectsLine CE))
    (hcdb : between c d b) :
    ¬(b.onLine DG) := by
  intro hbDG
  have hdb : d ≠ b := by euclid_finish
  have hcAB : c.onLine AB := by euclid_finish
  have step7_dfpar_boffDG_abdg : AB = DG := by sorry
  have step7_dfpar_boffDG_dgcene : DG ≠ CE := by sorry
  have hcDG : c.onLine DG := step7_dfpar_boffDG_abdg ▸ hcAB
  exact hDGCE (by
    euclid_apply (intersection_lines_common_point c DG CE)
    euclid_finish)

end Elements.Book2
