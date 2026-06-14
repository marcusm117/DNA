import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.9 (length): b and g (both on BF) are on the same side of EL. b,g are off EL
   (a common point of EL and BF would force them to meet, contradicting EL ∦ BF — EL ≠ BF since
   e ≠ b on EL∩BC while f on BF is off BC). Being off EL and not separable across it, share a side. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step9_len_ss (b d e f g : Point) (BC BF EL : Line)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC) (hbde : between b d e)
    (hbBF : b.onLine BF) (hgBF : g.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (heEL : e.onLine EL) (hELBF : ¬(EL.intersectsLine BF)) :
    b.sameSide g EL := by
  euclid_intros
  euclid_apply (between_symm b d e)
  have hboff : ¬(b.onLine EL) := by
    by_contra hbon
    euclid_apply (intersection_lines_common_point b EL BF)
    euclid_finish
  have hgoff : ¬(g.onLine EL) := by
    by_contra hgon
    euclid_apply (intersection_lines_common_point g EL BF)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing b g EL BF)
  euclid_finish

end Elements.Book2
