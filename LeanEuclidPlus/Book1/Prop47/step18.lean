import SystemE
import Book1.Prop17.Main
import Book1.Prop47.step17_ALCE
import Book1.Prop47.step17_ne_same
import Book1.Prop47.step18_bdec
import Book1.Prop47.step17_CL_pgram
import Book1.Prop47.step18_perp
import Book1.Prop47.step18_perpc
import Book1.Prop47.step18_blc
import Book1.Prop47.step18_dle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Square BDEC = parallelogram BL + parallelogram CL (split by the altitude at m∈BC, l∈DE);
-- BL = GB (step16), CL = HC (step17). sum_parallelograms_area + parallelogram_area glue them.
theorem helper_1_47_step18
    (a b c d e f g h k l m : Point) (AB BC AC DE BD CE AL : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (ha_AL : a.onLine AL) (hm_AL : m.onLine AL) (hm_BC : m.onLine BC)
    (hl_AL : l.onLine AL) (hl_DE : l.onLine DE)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hoffBD : ¬a.onLine BD) (h_a_nBC : ¬a.onLine BC) (h_d_nBC : ¬d.onLine BC)
    (h_cbd : (∠ c:b:d : ℝ) = ∟) (h_bce : (∠ b:c:e : ℝ) = ∟) (h_bac : (∠ b:a:c : ℝ) = ∟)
    (h_nd_same_a_BC : ¬d.sameSide a BC)
    (h_nDEBC : ¬DE.intersectsLine BC) (h_nBDCE : ¬BD.intersectsLine CE)
    (h_nALBD : ¬AL.intersectsLine BD)
    (step16 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b)
    (step17 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c) := by
  have hac : a ≠ c := by euclid_finish
  euclid_apply (proposition_17 b c a BC AC AB)
  have hacuteC : (∠ a:c:b : ℝ) < ∟ := by euclid_finish
  euclid_apply (proposition_17 c a b AC AB BC)
  have hacuteB : (∠ a:b:c : ℝ) < ∟ := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hce : c ≠ e := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have h_c_nBD : ¬c.onLine BD := by euclid_finish
  have h_e_nBC : ¬e.onLine BC := by euclid_finish
  have h_offCE : ¬a.onLine CE := by euclid_finish
  have hBCBD : BC ≠ BD := by euclid_finish
  have hALBD : AL ≠ BD := by euclid_finish
  have hBCCE : BC ≠ CE := by euclid_finish
  have hDEBC : DE ≠ BC := by euclid_finish
  have hBDCE : BD ≠ CE := by euclid_finish
  have step17_ALCE : ¬AL.intersectsLine CE := by euclid_apply (helper_1_47_step17_ALCE a b c AL CE BD BC (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)))
  have hALCE : AL ≠ CE := by euclid_finish
  have step17_ne_same : ¬e.sameSide a BC := by euclid_apply (helper_1_47_step17_ne_same a d e BC DE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬e.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)))
  have hbc : b ≠ c := by euclid_finish
  have ham : a ≠ m := by euclid_finish
  have hb_nAL : ¬b.onLine AL := by
    intro hb_AL
    euclid_apply (intersection_lines_common_point b AL BD)
    euclid_finish
  have hc_nAL : ¬c.onLine AL := by
    intro hc_AL
    euclid_apply (intersection_lines_common_point c AL CE)
    euclid_finish
  have hbm : b ≠ m := by euclid_finish
  have hcm : c ≠ m := by euclid_finish
  have hACBC : AC ≠ BC := by euclid_finish
  have step18_bdec : formParallelogram b c d e BC DE BD CE := by euclid_apply (helper_1_47_step18_bdec b c d e BC DE BD CE (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬e.onLine BC; assumption)) (by euclid_assumption "" (show DE ≠ BC; assumption)) (by euclid_assumption "" (show BD ≠ CE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)))
  have step17_CL_pgram : formParallelogram m l c e AL CE BC DE := by euclid_apply (helper_1_47_step17_CL_pgram a c e l m AL CE BC DE (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show ¬e.onLine BC; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)))
  have step18_perp : (∠ a:m:b : ℝ) = ∟ := by euclid_apply (helper_1_47_step18_perp a b c d m BC BD AL (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show a ≠ m; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b ≠ m; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show BC ≠ BD; assumption)) (by euclid_assumption "" (show AL ≠ BD; assumption)) (by euclid_assumption "" (show (∠ c:b:d : ℝ) = ∟; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)))
  have step18_perpc : (∠ a:m:c : ℝ) = ∟ := by euclid_apply (helper_1_47_step18_perpc a b c e m BC CE AL (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show a ≠ m; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show c ≠ m; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c ≠ e; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬e.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show BC ≠ CE; assumption)) (by euclid_assumption "" (show AL ≠ CE; assumption)) (by euclid_assumption "" (show (∠ b:c:e : ℝ) = ∟; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬e.sameSide a BC; assumption)))
  have step18_blc : between b m c := by euclid_apply (helper_1_47_step18_blc a b c m AB BC AC AL (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show AC ≠ BC; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show (∠ a:b:c : ℝ) < ∟; assumption)) (by euclid_assumption "" (show (∠ a:c:b : ℝ) < ∟; assumption)) (by euclid_assumption "" (show (∠ a:m:b : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:m:c : ℝ) = ∟; assumption)))
  have step18_dle : between d l e := by euclid_apply (helper_1_47_step18_dle a b c d e l m BC BD CE DE AL (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show between b m c; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine CE; assumption)))
  euclid_apply (sum_parallelograms_area b c d e m l BC DE BD CE)
  euclid_apply (parallelogram_area m l c e AL CE BC DE)
  euclid_finish

end Elements.Book1
