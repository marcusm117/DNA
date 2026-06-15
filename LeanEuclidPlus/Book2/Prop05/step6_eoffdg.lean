import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: e ∉ DG. e ∈ CE, DG ∥ CE (¬DG.intersectsLine CE) and DG ≠ CE (d ∈ DG, ¬d ∈ CE). A point
   on CE cannot lie on the parallel DG. (Mirror of Prop06 step7_eoffbg, relabel BG→DG.) -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_eoffdg (d e : Point) (CE DG : Line)
    (heCE : e.onLine CE) (hdDG : d.onLine DG)
    (hdoffCE : ¬(d.onLine CE))
    (hDGCE : ¬(DG.intersectsLine CE)) :
    ¬(e.onLine DG) := by
  intro heDG
  have hDGneCE : DG ≠ CE := fun heq => hdoffCE (heq ▸ hdDG)
  euclid_apply (intersection_lines_common_point e DG CE)
  euclid_finish

end Elements.Book2
