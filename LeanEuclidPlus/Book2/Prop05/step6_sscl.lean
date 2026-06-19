import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: c and l (both on CE) are on the same side of DG. (Mirror of Prop06 step7_sscl, relabel
   BG→DG.) c,l off DG (a common point of CE and DG would force them to meet, contra CE ∦ DG; DG ≠ CE
   since d ∈ DG, ¬d ∈ CE). Off DG and not separable ⟹ same side. -/
theorem helper_2_5_step6_sscl (c d l : Point) (CE DG : Line)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE) (hdDG : d.onLine DG)
    (hdoffCE : ¬(d.onLine CE))
    (hDGCE : ¬(DG.intersectsLine CE)) :
    c.sameSide l DG := by
  euclid_intros
  have hDGneCE : DG ≠ CE := fun heq => hdoffCE (heq ▸ hdDG)
  have hcoff : ¬(c.onLine DG) := by
    by_contra hcon
    euclid_apply (intersection_lines_common_point c DG CE)
    euclid_finish
  have hloff : ¬(l.onLine DG) := by
    by_contra hlon
    euclid_apply (intersection_lines_common_point l DG CE)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing c l DG CE)
  euclid_finish

end Elements.Book2
