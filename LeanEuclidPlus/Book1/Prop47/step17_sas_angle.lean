import SystemE
import Book1.Prop47.step17_hacuteC
import Book1.Prop47.step17_ss_aCE
import Book1.Prop47.step17_ss_bCK
import Book1.Prop47.step17_ne_same
import Book1.Prop47.step17_nk_same
import Book1.Prop47.step17_ss_eAC
import Book1.Prop47.step17_ss_kBC
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- ∠ECA = ∠ECB + ∠BCA = ∟ + ∠BCA;  ∠KCB = ∠KCA + ∠ACB = ∟ + ∠ACB;  ∠BCA = ∠ACB ⟹ ∠ECA = ∠BCK.
theorem helper_1_47_step17_sas_angle
    (a b c d e h k : Point) (AB AC CE CK BC DE HK : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hcb : c ≠ b)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hca : c ≠ a)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE) (hce : c ≠ e)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK) (hck : c ≠ k)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hh_HK : h.onLine HK) (hk_HK : k.onLine HK)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hBCCE : BC ≠ CE) (hACCK : AC ≠ CK)
    (h_a_nBC : ¬a.onLine BC) (h_b_nAC : ¬b.onLine AC)
    (h_d_nBC : ¬d.onLine BC) (h_e_nBC : ¬e.onLine BC)
    (h_h_nAC : ¬h.onLine AC) (h_k_nAC : ¬k.onLine AC)
    (h_a_nCE : ¬a.onLine CE) (h_b_nCK : ¬b.onLine CK)
    (h_b_nCE : ¬b.onLine CE) (h_a_nCK : ¬a.onLine CK)
    (h_nDEBC : ¬DE.intersectsLine BC) (h_nHKAC : ¬HK.intersectsLine AC)
    (h_nd_same_a_BC : ¬d.sameSide a BC) (h_nh_same_b_AC : ¬h.sameSide b AC)
    (h_bce : (∠ b:c:e : ℝ) = ∟) (h_ack : (∠ a:c:k : ℝ) = ∟)
    (h_bac : (∠ b:a:c : ℝ) = ∟) :
    ∠ e:c:a = ∠ b:c:k := by
  have step17_hacuteC : (∠ a:c:b : ℝ) < ∟ := by euclid_apply (helper_1_47_step17_hacuteC a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)))
  have step17_ss_aCE : a.sameSide b CE := by euclid_apply (helper_1_47_step17_ss_aCE a b c e BC CE (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c ≠ e; assumption)) (by euclid_assumption "" (show BC ≠ CE; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show (∠ b:c:e : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:c:b : ℝ) < ∟; assumption)))
  have step17_ss_bCK : b.sameSide a CK := by euclid_apply (helper_1_47_step17_ss_bCK a b c k AC CK (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show c ≠ k; assumption)) (by euclid_assumption "" (show AC ≠ CK; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine CK; assumption)) (by euclid_assumption "" (show (∠ a:c:k : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:c:b : ℝ) < ∟; assumption)))
  have step17_ne_same : ¬e.sameSide a BC := by euclid_apply (helper_1_47_step17_ne_same a d e BC DE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬e.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)))
  have step17_nk_same : ¬k.sameSide b AC := by euclid_apply (helper_1_47_step17_nk_same b h k AC HK (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬k.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.sameSide b AC; assumption)))
  have step17_ss_eAC : e.sameSide b AC := by euclid_apply (helper_1_47_step17_ss_eAC a b c e CE BC AC (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c ≠ e; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬e.sameSide a BC; assumption)) (by euclid_assumption "" (show a.sameSide b CE; assumption)))
  have step17_ss_kBC : k.sameSide a BC := by euclid_apply (helper_1_47_step17_ss_kBC a b c k CK AC BC (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c ≠ k; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬k.sameSide b AC; assumption)) (by euclid_assumption "" (show b.sameSide a CK; assumption)))
  euclid_apply (sum_angles_onlyif c e a b CE AC)
  euclid_apply (sum_angles_onlyif c k b a CK BC)
  euclid_finish

end Elements.Book1
