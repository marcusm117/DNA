import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- The parallelogram BMLD: m,l on AL; b,d on BD (AL ∥ BD); m,b on BC; l,d on DE (BC ∥ DE).
theorem helper_1_47_step13_pgram
    (a b d l m : Point) (AL BD BC DE : Line)
    (ha_AL : a.onLine AL) (hoffBD : ¬a.onLine BD)
    (hm_AL : m.onLine AL) (hl_AL : l.onLine AL)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hm_BC : m.onLine BC) (hb_BC : b.onLine BC)
    (hl_DE : l.onLine DE) (hd_DE : d.onLine DE)
    (h_d_nBC : ¬d.onLine BC)
    (h_nBDAL : ¬BD.intersectsLine AL) (h_nDEBC : ¬DE.intersectsLine BC) :
    formParallelogram m l b d AL BD BC DE := by
  have hALBD : AL ≠ BD := by euclid_finish
  have hDEBC : DE ≠ BC := by euclid_finish
  have h_d_nAL : ¬d.onLine AL := by
    intro hd_AL
    euclid_apply (intersection_lines_common_point d AL BD)
    euclid_finish
  have h_m_nDE : ¬m.onLine DE := by
    intro hm_DE
    euclid_apply (intersection_lines_common_point m DE BC)
    euclid_finish
  have h_b_nDE : ¬b.onLine DE := by
    intro hb_DE
    euclid_apply (intersection_lines_common_point b DE BC)
    euclid_finish
  have hld : l ≠ d := by euclid_finish
  have hmb_DE : m.sameSide b DE := by
    by_contra hcon
    euclid_apply (intersection_lines_opposing m b DE BC)
    euclid_finish
  euclid_finish

end Elements.Book1
