import SystemE
import Book1.Prop17.Main
import Book1.Prop47.step17_sas_angle
import Book1.Prop47.step17_sas
import Book1.Prop47.step17_CL
import Book1.Prop47.step17_HC
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Symmetric to steps 8–16: parallelogram CL = 2·△ACE, square HC = 2·△CBK, △ACE = △CBK ⟹ CL = HC.
theorem helper_1_47_step17
    (a b c d e h k l m : Point) (AB AC AL AE BK CE DE BC BD AH CK HK : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (ha_AL : a.onLine AL) (hm_AL : m.onLine AL) (hl_AL : l.onLine AL)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (hm_BC : m.onLine BC) (hc_BC : c.onLine BC) (hb_BC : b.onLine BC)
    (hl_DE : l.onLine DE) (he_DE : e.onLine DE) (hd_DE : d.onLine DE)
    (ha_AE : a.onLine AE) (he_AE : e.onLine AE)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (ha_AH : a.onLine AH) (hh_AH : h.onLine AH)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK)
    (hh_HK : h.onLine HK) (hk_HK : k.onLine HK)
    (hb_BK : b.onLine BK) (hk_BK : k.onLine BK)
    (hb_BD : b.onLine BD) (hoffBD : ¬a.onLine BD)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (h_a_nBC : ¬a.onLine BC) (h_b_nAC : ¬b.onLine AC)
    (h_d_nBC : ¬d.onLine BC)
    (h_h_nAC : ¬h.onLine AC)
    (h_nDEBC : ¬DE.intersectsLine BC) (h_nALBD : ¬AL.intersectsLine BD)
    (h_nBDCE : ¬BD.intersectsLine CE)
    (h_nAHCK : ¬AH.intersectsLine CK) (h_nHKAC : ¬HK.intersectsLine AC)
    (h_bah : between b a h)
    (hce_len : |(c─e)| = |(b─c)|) (hck_len : |(c─k)| = |(a─c)|)
    (h_bce : (∠ b:c:e : ℝ) = ∟) (h_ack : (∠ a:c:k : ℝ) = ∟)
    (h_bac : (∠ b:a:c : ℝ) = ∟)
    (h_nd_same_a_BC : ¬d.sameSide a BC) (h_nh_same_b_AC : ¬h.sameSide b AC) :
    Triangle.area △ c:e:l + Triangle.area △ c:l:m = Triangle.area △ a:h:k + Triangle.area △ a:k:c := by
  have hac : a ≠ c := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have hce : c ≠ e := by euclid_finish
  have hck : c ≠ k := by euclid_finish
  have h_c_nBD : ¬c.onLine BD := by euclid_finish
  euclid_apply (proposition_17 b c a BC AC AB)
  have hacuteC : (∠ a:c:b : ℝ) < ∟ := by euclid_finish
  have h_e_nBC : ¬e.onLine BC := by euclid_finish
  have h_k_nAC : ¬k.onLine AC := by euclid_finish
  have hBCCE : BC ≠ CE := by euclid_finish
  have hACCK : AC ≠ CK := by euclid_finish
  have h_offCE : ¬a.onLine CE := by euclid_finish
  have h_b_nCE : ¬b.onLine CE := by euclid_finish
  have h_a_nCK : ¬a.onLine CK := by euclid_finish
  have h_b_nCK : ¬b.onLine CK := by euclid_finish
  have h_k_nBC : ¬k.onLine BC := by euclid_finish
  have step17_sas_angle : ∠ e:c:a = ∠ b:c:k := by euclid_apply (helper_1_47_step17_sas_angle a b c d e h k AB AC CE CK BC DE HK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c ≠ e; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show c ≠ k; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show BC ≠ CE; assumption)) (by euclid_assumption "" (show AC ≠ CK; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬e.onLine BC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬k.onLine AC; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show ¬b.onLine CK; assumption)) (by euclid_assumption "" (show ¬b.onLine CE; assumption)) (by euclid_assumption "" (show ¬a.onLine CK; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬h.sameSide b AC; assumption)) (by euclid_assumption "" (show (∠ b:c:e : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:c:k : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)))
  have step17_sas : Triangle.area △ a:c:e = Triangle.area △ c:b:k := by euclid_apply (helper_1_47_step17_sas a b c e k CE AE AC BC BK CK (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine BK; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show |(c─e)| = |(b─c)|; assumption)) (by euclid_assumption "" (show |(c─k)| = |(a─c)|; assumption)) (by euclid_assumption "" (show ∠ e:c:a = ∠ b:c:k; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show ¬k.onLine BC; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)))
  have step17_CL : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:c:e + Triangle.area △ a:c:e := by euclid_apply (helper_1_47_step17_CL a b c e l m AC CE BC DE AL AE BD (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬e.onLine BC; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)))
  have step17_HC : Triangle.area △ a:h:k + Triangle.area △ a:k:c =
      Triangle.area △ c:b:k + Triangle.area △ c:b:k := by euclid_apply (helper_1_47_step17_HC a b c h k AC AH CK HK BK BC (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine BK; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine CK; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)) (by euclid_assumption "" (show between b a h; assumption)))
  euclid_finish

end Elements.Book1
