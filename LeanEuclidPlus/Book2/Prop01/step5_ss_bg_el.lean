import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.5: b and g (both on the left vertical BF) are on the same side of the EL
   vertical. b,g are off EL (a common point of EL and BF would force them to meet, contradicting
   EL ∦ BF — EL ≠ BF since e ≠ b sits on EL∩BC while b on BF is off EL). Being off EL and not
   separable across it (BF ∦ EL), b and g share a side. -/
theorem helper_2_1_step5_ss_bg_el (b e f g : Point) (BC BF EL : Line)
    (hbBC : b.onLine BC) (heBC : e.onLine BC) (hbe : b ≠ e)
    (hbBF : b.onLine BF) (hgBF : g.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (heEL : e.onLine EL) (hELBF : ¬(EL.intersectsLine BF)) :
    b.sameSide g EL := by
  euclid_intros
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
