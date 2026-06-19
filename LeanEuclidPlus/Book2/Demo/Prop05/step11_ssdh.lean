import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: d.sameSide h CE. d ∈ DG; h ∈ DG; DG ∥ CE. d ∉ CE (step11_doffCE) gives DG ≠ CE.
   Mirror of Prop06 step9_ssdk / step6_sshg pattern. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_ssdh (d h : Point) (DG CE : Line)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hdoffCE : ¬(d.onLine CE))
    (hDGCE : ¬(DG.intersectsLine CE)) :
    d.sameSide h CE := by
  euclid_intros
  have hDGneCE : DG ≠ CE := fun heq => hdoffCE (heq ▸ hdDG)
  have hdoff : ¬(d.onLine CE) := hdoffCE
  have hhoff : ¬(h.onLine CE) := by
    by_contra hhon
    euclid_apply (intersection_lines_common_point h DG CE)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing d h CE DG)
  euclid_finish

end Elements.Book2
