import SystemE
import Book3.Prop33.hFG_int_AE_hd_offAB
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- e0 is off AB: if e0 were on AB, then a, e0, b are collinear, so the ray a→e0 is either the
-- ray a→b (¬between e0 a b, giving ∠d:a:e0 = ∠d:a:b) or its opposite (between e0 a b, giving
-- ∠d:a:e0 = ∠d:a:b too by perpendicular_onlyif) — either way ∟ = ∠d:a:b < ∟, a contradiction.
theorem helper_3_33_hFG_int_AE_he0off
    (a b c₁ c c₂ d e0 : Point) (AD AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0offAD : ¬ e0.onLine AD)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟) :
    ¬ e0.onLine AB := by
  intro he0AB
  have hFG_int_AE_hd_offAB : ¬ d.onLine AB := by euclid_apply (helper_3_33_hFG_int_AE_hd_offAB a b c₁ c c₂ d AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
  by_cases hbet : between e0 a b
  · euclid_apply (perpendicular_onlyif e0 b a d AB)
    euclid_finish
  · euclid_apply (equal_angles a e0 b d d AB AD)
    euclid_finish

end Elements.Book3
