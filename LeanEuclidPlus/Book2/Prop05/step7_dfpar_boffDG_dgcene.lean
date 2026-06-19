import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- DG ≠ CE from ¬(DG.intersectsLine CE) + d∈DG, d∈AB=DG (abdg), c∈CE, c∈AB, between c d b. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_boffDG_dgcene (b c d : Point) (AB CE DG : Line)
    (hdDG : d.onLine DG) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (hcAB : c.onLine AB)
    (hDGCE : ¬(DG.intersectsLine CE))
    (hABDG : AB = DG)
    (hcdb : between c d b) :
    DG ≠ CE := by
  euclid_intros
  euclid_finish

end Elements.Book2
