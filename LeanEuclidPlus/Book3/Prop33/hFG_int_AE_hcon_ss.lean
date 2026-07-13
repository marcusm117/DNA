import SystemE
import Book3.Prop33.hFG_int_AE_hcon_ss_a
import Book3.Prop33.hFG_int_AE_hcon_ss_b
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- ∠e0:a:b = ∟ and b on the same side of AE as d; ∠d:a:b would be 0.  Split on e0's side of AB.
theorem helper_3_33_hFG_int_AE_hcon_ss
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (heq : ∠ e0:a:b = ∟) (hbd : b.sameSide d AE) :
    False := by
  by_cases h2 : e0.sameSide d AB
  · have hFG_int_AE_hcon_ss_a : False := by euclid_apply (helper_3_33_hFG_int_AE_hcon_ss_a a b c₁ c c₂ d e0 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show ∠ e0:a:b = ∟; assumption)) (by euclid_assumption "" (show b.sameSide d AE; assumption)) (by euclid_assumption "" (show e0.sameSide d AB; assumption)))
    exact hFG_int_AE_hcon_ss_a
  · have hFG_int_AE_hcon_ss_b : False := by euclid_apply (helper_3_33_hFG_int_AE_hcon_ss_b a b c₁ c c₂ d e0 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show ∠ e0:a:b = ∟; assumption)) (by euclid_assumption "" (show b.sameSide d AE; assumption)) (by euclid_assumption "" (show ¬ e0.sameSide d AB; assumption)))
    exact hFG_int_AE_hcon_ss_b

end Elements.Book3
