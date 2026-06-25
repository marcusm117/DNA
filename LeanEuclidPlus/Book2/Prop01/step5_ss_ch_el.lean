import SystemE
import Book2.Prop01.step5_ss_ch_el_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.5: c and h (both on the right vertical CH) are on the same side of the EL
   vertical. CH ∦ EL (sub-node step5_ss_ch_el_par, via proposition_30 since both ∦ BF). c,h are
   off EL (a common point of EL and CH would force them to meet, contradicting CH ∦ EL — CH ≠ EL
   since e ≠ c sits on EL∩BC while c on CH is off EL). Being off EL and not separable across it,
   c and h share a side. -/
theorem helper_2_1_step5_ss_ch_el (b c e f h : Point) (BC BF EL CH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (heBC : e.onLine BC)
    (hbc : b ≠ c) (hbe : b ≠ e) (hec : e ≠ c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hcCH : c.onLine CH) (hhCH : h.onLine CH) (hhoffBC : ¬(h.onLine BC))
    (heEL : e.onLine EL) (hELBF : ¬(EL.intersectsLine BF)) (hCHBF : ¬(CH.intersectsLine BF)) :
    c.sameSide h EL := by
  euclid_intros
  have step5_ss_ch_el_par : ¬(CH.intersectsLine EL) := by euclid_apply (helper_2_1_step5_ss_ch_el_par b c e f h BC BF EL CH (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hcoff : ¬(c.onLine EL) := by
    by_contra hcon
    euclid_apply (intersection_lines_common_point c EL CH)
    euclid_finish
  have hhoff : ¬(h.onLine EL) := by
    by_contra hhon
    euclid_apply (intersection_lines_common_point h EL CH)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing c h EL CH)
  euclid_finish

end Elements.Book2
