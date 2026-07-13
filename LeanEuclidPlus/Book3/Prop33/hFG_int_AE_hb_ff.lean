import SystemE
import Book3.Prop33.hFG_int_AE_hb_offAD
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- e1 is the reflection of e0 across a on AE (between e0 a e1); a is on AD so e0, e1 are on
-- opposite sides of AD.  b is opposite e0 across AD (¬h4), hence on the same side as e1.
theorem helper_3_33_hFG_int_AE_hb_ff
    (a b c₁ c c₂ d e0 e1 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE) (he1ae : e1.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (he1 : between e0 a e1) (h4 : ¬ b.sameSide e0 AD) :
    b.sameSide e1 AD := by
  have hFG_int_AE_hb_offAD : ¬ b.onLine AD := by euclid_apply (helper_3_33_hFG_int_AE_hb_offAD a b c₁ c c₂ d AD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
  euclid_finish

end Elements.Book3
