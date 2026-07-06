import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_hALDE
    (a b c d e : Point) (AB BC AC AL BD DE : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hACAB : AC ≠ AB)
    (ha_AL : a.onLine AL) (h_nALBD : ¬AL.intersectsLine BD) (hoffBD : ¬a.onLine BD)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hbd_len : |(b─d)| = |(b─c)|) (hde_len : |(d─e)| = |(b─c)|)
    (h_bde : (∠ b:d:e : ℝ) = ∟) :
    AL.intersectsLine DE := by
  by_contra hcon
  have hbc : b ≠ c := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hdAL : ¬d.onLine AL := by
    intro hd_AL
    euclid_apply (intersection_lines_common_point d AL BD)
    euclid_finish
  euclid_apply (parallel_line_unique d AL BD DE)
  have hbDE : b.onLine DE := by euclid_finish
  by_cases hbtw : between b d e
  · euclid_apply (flat_angle_onlyif b d e)
    euclid_finish
  · euclid_apply (degenerated_angle_if d b e DE)
    euclid_finish

end Elements.Book1
