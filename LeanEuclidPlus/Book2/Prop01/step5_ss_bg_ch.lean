import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.5: b and g (both on the left vertical BF) are on the same side of the right
   vertical CH. b,g are off CH (a common point of CH and BF would force them to meet, contradicting
   CH ∦ BF — CH ≠ BF since c ≠ b on CH∩BC while f on BF is off BC). Being off CH and not separable
   across it (BF ∦ CH), b and g share a side. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step5_ss_bg_ch (b c f g : Point) (BC BF CH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hbc : b ≠ c)
    (hbBF : b.onLine BF) (hgBF : g.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hcCH : c.onLine CH) (hCHBF : ¬(CH.intersectsLine BF)) :
    b.sameSide g CH := by
  euclid_intros
  have hboff : ¬(b.onLine CH) := by
    by_contra hbon
    euclid_apply (intersection_lines_common_point b CH BF)
    euclid_finish
  have hgoff : ¬(g.onLine CH) := by
    by_contra hgon
    euclid_apply (intersection_lines_common_point g CH BF)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing b g CH BF)
  euclid_finish

end Elements.Book2
