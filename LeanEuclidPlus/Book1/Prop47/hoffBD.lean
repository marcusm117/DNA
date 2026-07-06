import SystemE
import Book1.Prop47.hoffBD_hacute
import Book1.Prop47.hoffBD_bet
import Book1.Prop47.hoffBD_nbet
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_hoffBD
    (a b c : Point) (AB BC AC : Line)
    (d : Point) (BD : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (h_bac : (∠ b:a:c : ℝ) = ∟)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (h_cbd : (∠ c:b:d : ℝ) = ∟)
    (hbd_len : |(b─d)| = |(b─c)|) :
    ¬a.onLine BD := by
  by_contra h
  have hbc : b ≠ c := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hoffBD_hacute : (∠ a:b:c : ℝ) < ∟ := by euclid_apply (helper_1_47_hoffBD_hacute a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)))
  by_cases hbet : between a b d
  · have hoffBD_bet : False := by euclid_apply (helper_1_47_hoffBD_bet a b c d AB BC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show (∠ c:b:d : ℝ) = ∟; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show (∠ a:b:c : ℝ) < ∟; assumption)))
    exact hoffBD_bet
  · have hoffBD_nbet : False := by euclid_apply (helper_1_47_hoffBD_nbet a b c d BC BD (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show (∠ c:b:d : ℝ) = ∟; assumption)) (by euclid_assumption "" (show ¬between a b d; assumption)) (by euclid_assumption "" (show (∠ a:b:c : ℝ) < ∟; assumption)))
    exact hoffBD_nbet

end Elements.Book1
