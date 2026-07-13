import SystemE
import Book3.Prop33.hFG_int_AE_hd_offAB
import Book3.Prop33.hFG_int_AE_he0_offAB
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- e1 is the reflection of e0 across a on AE; a is on AB so e0, e1 are on opposite sides of AB.
-- d is opposite e0 across AB (¬h5), hence on the same side as e1.  (d is off AB via hFG_int_AE_hd_offAB.)
theorem helper_3_33_hFG_int_AE_hd_ff
    (a b c₁ c c₂ d e0 e1 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE) (he1ae : e1.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a) (heq : ∠ e0:a:b = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (he1 : between e0 a e1) (h5 : ¬ d.sameSide e0 AB) :
    d.sameSide e1 AB := by
  have hFG_int_AE_hd_offAB : ¬ d.onLine AB := by euclid_apply (helper_3_33_hFG_int_AE_hd_offAB a b c₁ c c₂ d AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
  have hFG_int_AE_he0_offAB : ¬ e0.onLine AB := by euclid_apply (helper_3_33_hFG_int_AE_he0_offAB a b c₁ c c₂ e0 AD AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ e0:a:b = ∟; assumption)))
  euclid_finish

end Elements.Book3
