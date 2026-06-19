import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- AB = DG from b∈AB∩DG, d∈AB∩DG, d≠b. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_boffDG_abdg (b d : Point) (AB DG : Line)
    (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hbDG : b.onLine DG) (hdDG : d.onLine DG)
    (hdb : d ≠ b) :
    AB = DG := by
  euclid_apply (two_points_determine_line b d AB DG)
  euclid_finish

end Elements.Book2
