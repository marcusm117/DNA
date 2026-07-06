import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Ported helper_47_between_dle (l'=m): d∈BD∥AL same side as b, e∈CE∥AL same side as c; b,c opposite
-- across AL (between b m c, m∈AL) ⟹ d,e opposite ⟹ AL meets DE at l ⟹ between d l e.
theorem helper_1_47_step18_dle
    (a b c d e l m : Point) (BC BD CE DE AL : Line)
    (ha_AL : a.onLine AL) (h_a_nBD : ¬a.onLine BD) (h_a_nCE : ¬a.onLine CE)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hb_BD : b.onLine BD) (hc_CE : c.onLine CE)
    (hd_BD : d.onLine BD) (he_CE : e.onLine CE)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hde : d ≠ e)
    (hl_AL : l.onLine AL) (hl_DE : l.onLine DE)
    (hm_AL : m.onLine AL) (hm_BC : m.onLine BC)
    (h_bmc : between b m c)
    (h_nALBD : ¬AL.intersectsLine BD) (h_nALCE : ¬AL.intersectsLine CE) :
    between d l e := by
  have hALBD : AL ≠ BD := by euclid_finish
  have hALCE : AL ≠ CE := by euclid_finish
  have hbAL : ¬b.onLine AL := by
    by_contra
    euclid_apply (intersection_lines_common_point b AL BD)
    euclid_finish
  have hcAL : ¬c.onLine AL := by
    by_contra
    euclid_apply (intersection_lines_common_point c AL CE)
    euclid_finish
  have hdAL : ¬d.onLine AL := by
    by_contra
    euclid_apply (intersection_lines_common_point d AL BD)
    euclid_finish
  have heAL : ¬e.onLine AL := by
    by_contra
    euclid_apply (intersection_lines_common_point e AL CE)
    euclid_finish
  have hdb : d.sameSide b AL := by
    by_contra
    euclid_apply (intersection_lines_opposing d b AL BD)
    euclid_finish
  have hec : e.sameSide c AL := by
    by_contra
    euclid_apply (intersection_lines_opposing e c AL CE)
    euclid_finish
  euclid_apply (pasch_3 b m c AL)
  have hde2 : ¬d.sameSide e AL := by euclid_finish
  euclid_apply (pasch_4 d l e AL DE)
  euclid_finish

end Elements.Book1
