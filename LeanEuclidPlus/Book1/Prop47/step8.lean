import SystemE
import Book1.Prop47.step8_hacute
import Book1.Prop47.step8_hA11
import Book1.Prop47.step8_hA10
import Book1.Prop47.step8_hC11
import Book1.Prop47.step8_hf_nsame
import Book1.Prop47.step8_hC10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8
    (a b c d f g : Point) (AB BC AC BD BF GF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hb_BF : b.onLine BF) (hf_BF : f.onLine BF) (hfb : f ≠ b)
    (hf_GF : f.onLine GF) (hg_GF : g.onLine GF)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hoffBD : ¬a.onLine BD)
    (h_c_nAB : ¬c.onLine AB) (h_a_nBC : ¬a.onLine BC) (h_d_nBC : ¬d.onLine BC)
    (h_nd_same_a_BC : ¬d.sameSide a BC)
    (h_nGFAB : ¬GF.intersectsLine AB) (hg_nAB : ¬g.onLine AB) (h_ng_same_c_AB : ¬g.sameSide c AB)
    (h_bac : (∠ b:a:c : ℝ) = ∟) (h_cbd : (∠ c:b:d : ℝ) = ∟) (h_abf : (∠ a:b:f : ℝ) = ∟)
    (h_dbc_eq_fba : ∠ d:b:c = ∠ f:b:a) :
    ∠ d:b:a = ∠ f:b:c := by
  have step8_hacute : (∠ a:b:c : ℝ) < ∟ := by euclid_apply (helper_1_47_step8_hacute a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)))
  have hBCBD : BC ≠ BD := by euclid_finish
  have hABBF : AB ≠ BF := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hc_nBD : ¬c.onLine BD := by euclid_finish
  have hc_nBF : ¬c.onLine BF := by euclid_finish
  have hf_nAB : ¬f.onLine AB := by euclid_finish
  have step8_hA11 : a.sameSide c BD := by euclid_apply (helper_1_47_step8_hA11 a b c d BC BD (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show BC ≠ BD; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show (∠ c:b:d : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:b:c : ℝ) < ∟; assumption)))
  have step8_hA10 : d.sameSide c AB := by euclid_apply (helper_1_47_step8_hA10 a b c d AB BC BD (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show a.sameSide c BD; assumption)))
  have step8_hC11 : c.sameSide a BF := by euclid_apply (helper_1_47_step8_hC11 a b c f AB BF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show AB ≠ BF; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show ¬c.onLine BF; assumption)) (by euclid_assumption "" (show (∠ a:b:f : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:b:c : ℝ) < ∟; assumption)))
  have step8_hf_nsame : ¬f.sameSide c AB := by euclid_apply (helper_1_47_step8_hf_nsame a b c f g AB GF (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show ¬GF.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬f.onLine AB; assumption)) (by euclid_assumption "" (show ¬g.onLine AB; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show ¬g.sameSide c AB; assumption)))
  have step8_hC10 : f.sameSide a BC := by euclid_apply (helper_1_47_step8_hC10 a b c f AB BC BF (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show ¬f.sameSide c AB; assumption)) (by euclid_assumption "" (show c.sameSide a BF; assumption)))
  euclid_apply (sum_angles_onlyif b d a c BD AB)
  euclid_apply (sum_angles_onlyif b f c a BF BC)
  euclid_finish

end Elements.Book1
