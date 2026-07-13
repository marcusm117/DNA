import SystemE
import Book3.Prop33.hFG_int_AE_hos_tt
import Book3.Prop33.hFG_int_AE_hos_tf
import Book3.Prop33.hFG_int_AE_hos_ft
import Book3.Prop33.hFG_int_AE_hos_ff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- b and d on OPPOSITE sides of AE, both ⊥ ray ae0 at a: rays ab, ad are opposite, ∠b:a:d = 2∟.
-- Pin e0's sides of AD and AB (4 corners) so the interior-ray (e0 or its reflection e1) has
-- both sum_angles_onlyif conditions available.
theorem helper_3_33_hFG_int_AE_hcon_os
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (heq : ∠ e0:a:b = ∟) (hbd : ¬ b.sameSide d AE) :
    False := by
  by_cases h4 : b.sameSide e0 AD
  · by_cases h5 : d.sameSide e0 AB
    · have hFG_int_AE_hos_tt : False := by euclid_apply (helper_3_33_hFG_int_AE_hos_tt a b c₁ c c₂ d e0 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show ∠ e0:a:b = ∟; assumption)) (by euclid_assumption "" (show ¬ b.sameSide d AE; assumption)) (by euclid_assumption "" (show b.sameSide e0 AD; assumption)) (by euclid_assumption "" (show d.sameSide e0 AB; assumption)))
      exact hFG_int_AE_hos_tt
    · have hFG_int_AE_hos_tf : False := by euclid_apply (helper_3_33_hFG_int_AE_hos_tf a b c₁ c c₂ d e0 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show ∠ e0:a:b = ∟; assumption)) (by euclid_assumption "" (show ¬ b.sameSide d AE; assumption)) (by euclid_assumption "" (show b.sameSide e0 AD; assumption)) (by euclid_assumption "" (show ¬ d.sameSide e0 AB; assumption)))
      exact hFG_int_AE_hos_tf
  · by_cases h5 : d.sameSide e0 AB
    · have hFG_int_AE_hos_ft : False := by euclid_apply (helper_3_33_hFG_int_AE_hos_ft a b c₁ c c₂ d e0 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show ∠ e0:a:b = ∟; assumption)) (by euclid_assumption "" (show ¬ b.sameSide d AE; assumption)) (by euclid_assumption "" (show ¬ b.sameSide e0 AD; assumption)) (by euclid_assumption "" (show d.sameSide e0 AB; assumption)))
      exact hFG_int_AE_hos_ft
    · have hFG_int_AE_hos_ff : False := by euclid_apply (helper_3_33_hFG_int_AE_hos_ff a b c₁ c c₂ d e0 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show ∠ e0:a:b = ∟; assumption)) (by euclid_assumption "" (show ¬ b.sameSide d AE; assumption)) (by euclid_assumption "" (show ¬ b.sameSide e0 AD; assumption)) (by euclid_assumption "" (show ¬ d.sameSide e0 AB; assumption)))
      exact hFG_int_AE_hos_ff

end Elements.Book3
