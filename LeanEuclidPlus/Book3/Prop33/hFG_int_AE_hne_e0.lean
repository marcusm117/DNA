import SystemE
import Book3.Prop33.hFG_int_AE_hcon_ss
import Book3.Prop33.hFG_int_AE_hcon_os
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- ∠e0:a:b ≠ ∟: if ∠e0:a:b = ∟ then ray ab ⊥ AE at a; with ray ad ⊥ AE at a (∠d:a:e0 = ∟),
-- rays ab, ad coincide (∠d:a:b = 0) or are opposite (∠d:a:b = 2∟) — both contradict 0<∠d:a:b<∟.
theorem helper_3_33_hFG_int_AE_hne_e0
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟) :
    ∠ e0:a:b ≠ ∟ := by
  intro heq
  by_cases hbd : b.sameSide d AE
  · have hFG_int_AE_hcon_ss : False := by euclid_apply (helper_3_33_hFG_int_AE_hcon_ss a b c₁ c c₂ d e0 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show ∠ e0:a:b = ∟; assumption)) (by euclid_assumption "" (show b.sameSide d AE; assumption)))
    exact hFG_int_AE_hcon_ss
  · have hFG_int_AE_hcon_os : False := by euclid_apply (helper_3_33_hFG_int_AE_hcon_os a b c₁ c c₂ d e0 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show ∠ e0:a:b = ∟; assumption)) (by euclid_assumption "" (show ¬ b.sameSide d AE; assumption)))
    exact hFG_int_AE_hcon_os

end Elements.Book3
