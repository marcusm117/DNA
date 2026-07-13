import SystemE
import Book3.Prop33.hFG_int_AE_he0off
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- e ≠ b: e ∈ AE and b ∈ AB; if e = b then b ∈ AE ∩ AB = {a} (AE ≠ AB since e0 ∉ AB), so b = a,
-- contradicting a ≠ b.
theorem helper_3_33_heb
    (a b c₁ c c₂ d e0 e : Point) (AB AD AE : Line)
    (hne : a ≠ b) (hc1c : c₁ ≠ c) (hcc2 : c ≠ c₂) (hpos : 0 < ∠ c₁:c:c₂) (hacute : ∠ c₁:c:c₂ < ∟)
    (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (haab : a.onLine AB) (hbab : b.onLine AB)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0offAD : ¬ e0.onLine AD)
    (hperp_e : ∠ d:a:e0 = ∟) (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hadd : d ≠ a)
    (haAE : a.onLine AE) (he0AE : e0.onLine AE) (heAE : e.onLine AE) :
    e ≠ b := by
  have hFG_int_AE_he0off : ¬ e0.onLine AB := by euclid_apply (helper_3_33_hFG_int_AE_he0off a b c₁ c c₂ d e0 AD AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
  euclid_finish

end Elements.Book3
