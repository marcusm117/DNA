import SystemE
import Book1.Prop47.step18_bdec
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Square BDEC has area |BC|² (rectangle_area on the square: side |BD| = |BC|).
theorem helper_1_47_step19
    (b c d e : Point) (BC DE BD CE : Line)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (h_d_nBC : ¬d.onLine BC)
    (h_cbd : (∠ c:b:d : ℝ) = ∟) (h_bde : (∠ b:d:e : ℝ) = ∟)
    (hbd_len : |(b─d)| = |(b─c)|)
    (h_nDEBC : ¬DE.intersectsLine BC) (h_nBDCE : ¬BD.intersectsLine CE) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)| := by
  have hDEBC : DE ≠ BC := by euclid_finish
  have h_e_nBC : ¬e.onLine BC := by
    intro he_BC
    euclid_apply (intersection_lines_common_point e DE BC)
    euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hBDCE : BD ≠ CE := by euclid_finish
  have step18_bdec : formParallelogram b c d e BC DE BD CE := by euclid_apply (helper_1_47_step18_bdec b c d e BC DE BD CE (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬e.onLine BC; assumption)) (by euclid_assumption "" (show DE ≠ BC; assumption)) (by euclid_assumption "" (show BD ≠ CE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)))
  euclid_apply (rectangle_area b c d e BC DE BD CE)
  euclid_finish

end Elements.Book1
