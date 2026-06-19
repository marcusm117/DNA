import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: h and g (both on DG) are on the same side of BF. (Mirror of Prop06 step7_sshg, relabel
   BG→DG, DF→BF.) h,g off BF (a common point of DG and BF would force them to meet, contra DG ∦ BF;
   DG ≠ BF since d ∈ DG, ¬d ∈ BF). Off BF and not separable ⟹ same side. -/
theorem helper_2_5_step6_sshg (d g h : Point) (DG BF : Line)
    (hhDG : h.onLine DG) (hgDG : g.onLine DG) (hdDG : d.onLine DG)
    (hdoffBF : ¬(d.onLine BF))
    (hDGBF : ¬(DG.intersectsLine BF)) :
    h.sameSide g BF := by
  euclid_intros
  have hDGneBF : DG ≠ BF := fun heq => hdoffBF (heq ▸ hdDG)
  have hhoff : ¬(h.onLine BF) := by
    by_contra hhon
    euclid_apply (intersection_lines_common_point h BF DG)
    euclid_finish
  have hgoff : ¬(g.onLine BF) := by
    by_contra hgon
    euclid_apply (intersection_lines_common_point g BF DG)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing h g BF DG)
  euclid_finish

end Elements.Book2
