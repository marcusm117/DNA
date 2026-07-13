import SystemE
import Book3.Prop33.hFG_int_AE_he0off
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- ∠AFG = ∠BFG : since ∠a:f:g = ∟ (step5) and f is between a, b on AB with g off AB,
-- perpendicular_onlyif gives ∠a:f:g = ∠g:f:b = ∠b:f:g.
theorem helper_3_33_step8
    (a b c₁ c c₂ d e0 f g : Point) (AB AD AE : Line)
    (hne : a ≠ b) (hc1c : c₁ ≠ c) (hcc2 : c ≠ c₂) (hpos : 0 < ∠ c₁:c:c₂) (hacute : ∠ c₁:c:c₂ < ∟)
    (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (haab : a.onLine AB) (hbab : b.onLine AB)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0offAD : ¬ e0.onLine AD)
    (hperp_e : ∠ d:a:e0 = ∟) (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hadd : d ≠ a)
    (haAE : a.onLine AE) (he0AE : e0.onLine AE) (hgAE : g.onLine AE) (hga : g ≠ a)
    (hafb : between a f b) (step5 : ∠ a:f:g = ∟) :
    ∠ a:f:g = ∠ b:f:g := by
  have hFG_int_AE_he0off : ¬ e0.onLine AB := by euclid_apply (helper_3_33_hFG_int_AE_he0off a b c₁ c c₂ d e0 AD AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
  have hgoffAB : ¬ g.onLine AB := by euclid_finish
  euclid_apply (perpendicular_onlyif a b f g AB)
  euclid_finish

end Elements.Book3
