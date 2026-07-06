import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Parallelogram CMLE (mirror of step13_pgram): m,l on AL; c,e on CE (AL ∥ CE); m,c on BC; l,e on DE (BC ∥ DE).
theorem helper_1_47_step17_CL_pgram
    (a c e l m : Point) (AL CE BC DE : Line)
    (ha_AL : a.onLine AL) (h_offCE : ¬a.onLine CE)
    (hm_AL : m.onLine AL) (hl_AL : l.onLine AL)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (hm_BC : m.onLine BC) (hc_BC : c.onLine BC)
    (hl_DE : l.onLine DE) (he_DE : e.onLine DE)
    (h_e_nBC : ¬e.onLine BC)
    (h_nALCE : ¬AL.intersectsLine CE) (h_nDEBC : ¬DE.intersectsLine BC) :
    formParallelogram m l c e AL CE BC DE := by
  have hALCE : AL ≠ CE := by euclid_finish
  have hDEBC : DE ≠ BC := by euclid_finish
  have h_e_nAL : ¬e.onLine AL := by
    intro he_AL
    euclid_apply (intersection_lines_common_point e AL CE)
    euclid_finish
  have h_m_nDE : ¬m.onLine DE := by
    intro hm_DE
    euclid_apply (intersection_lines_common_point m DE BC)
    euclid_finish
  have h_c_nDE : ¬c.onLine DE := by
    intro hc_DE
    euclid_apply (intersection_lines_common_point c DE BC)
    euclid_finish
  have hle : l ≠ e := by euclid_finish
  have hmc_DE : m.sameSide c DE := by
    by_contra hcon
    euclid_apply (intersection_lines_opposing m c DE BC)
    euclid_finish
  euclid_finish

end Elements.Book1
