import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- The square BDEC: b,c on BC; d,e on DE (BC ∥ DE); b,d on BD; c,e on CE (BD ∥ CE).
theorem helper_1_47_step18_bdec
    (b c d e : Point) (BC DE BD CE : Line)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (h_d_nBC : ¬d.onLine BC) (h_e_nBC : ¬e.onLine BC)
    (hDEBC : DE ≠ BC) (hBDCE : BD ≠ CE)
    (h_nDEBC : ¬DE.intersectsLine BC) (h_nBDCE : ¬BD.intersectsLine CE) :
    formParallelogram b c d e BC DE BD CE := by
  have h_c_nDE : ¬c.onLine DE := by
    intro hc_DE
    euclid_apply (intersection_lines_common_point c DE BC)
    euclid_finish
  have h_b_nCE : ¬b.onLine CE := by
    intro hb_CE
    euclid_apply (intersection_lines_common_point b CE BD)
    euclid_finish
  have h_d_nCE : ¬d.onLine CE := by
    intro hd_CE
    euclid_apply (intersection_lines_common_point d CE BD)
    euclid_finish
  have hce : c ≠ e := by euclid_finish
  have hbd_CE : b.sameSide d CE := by
    by_contra hcon
    euclid_apply (intersection_lines_opposing b d CE BD)
    euclid_finish
  euclid_finish

end Elements.Book1
