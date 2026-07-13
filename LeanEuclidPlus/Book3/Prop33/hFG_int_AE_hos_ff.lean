import SystemE
import Book3.Prop33.hFG_int_AE_hb_ff
import Book3.Prop33.hFG_int_AE_hd_ff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- b,d opposite sides of AE; b opposite e0 across AD and d opposite e0 across AB.  The reflection
-- e1 (between e0 a e1) is the interior ray: b.sameSide e1 AD, d.sameSide e1 AB, and
-- ∠b:a:e1 = ∠d:a:e1 = ∟, so ∠b:a:d = ∠b:a:e1 + ∠e1:a:d = 2∟, contradicting ∠d:a:b < ∟.
theorem helper_3_33_hFG_int_AE_hos_ff
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (heq : ∠ e0:a:b = ∟) (hbd : ¬ b.sameSide d AE)
    (h4 : ¬ b.sameSide e0 AD) (h5 : ¬ d.sameSide e0 AB) :
    False := by
  euclid_apply (extend_point AE e0 a) as e1
  have hFG_int_AE_hb_ff : b.sameSide e1 AD := by euclid_apply (helper_3_33_hFG_int_AE_hb_ff a b c₁ c c₂ d e0 e1 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e1.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show between e0 a e1; assumption)) (by euclid_assumption "" (show ¬ b.sameSide e0 AD; assumption)))
  have hFG_int_AE_hd_ff : d.sameSide e1 AB := by euclid_apply (helper_3_33_hFG_int_AE_hd_ff a b c₁ c c₂ d e0 e1 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e1.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ e0:a:b = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show between e0 a e1; assumption)) (by euclid_assumption "" (show ¬ d.sameSide e0 AB; assumption)))
  euclid_apply (perpendicular_onlyif e0 e1 a b AE)
  euclid_apply (perpendicular_onlyif e0 e1 a d AE)
  euclid_apply (sum_angles_onlyif a b d e1 AB AD)
  euclid_finish

end Elements.Book3
