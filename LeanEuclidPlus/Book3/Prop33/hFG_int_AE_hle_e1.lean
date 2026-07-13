import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop33.hFG_int_AE_hsup_e1
import Book3.Prop33.hFG_int_AE_hne_e0
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- In the branch ∠e0:a:b ≥ ∟, the AE-extension e1 (a between e0, e1) is the acute rep.
-- ∠e0:a:b + ∠e1:a:b = 2∟ (straight line e0-a-e1, b off it), and ∠e0:a:b ≠ ∟ (else AE ⊥ AB,
-- which with AD ⊥ AE forces ∠d:a:b ∈ {0,2∟}), so ∠e0:a:b > ∟ and ∠e1:a:b < ∟.
theorem helper_3_33_hFG_int_AE_hle_e1
    (a b c₁ c c₂ d e0 e1 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hadd : d ≠ a) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE) (he1ae : e1.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (he0offAB : ¬ e0.onLine AB)
    (he1 : between e0 a e1) (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (hpe2 : ¬ ∠ e0:a:b < ∟) :
    ∠ e1:a:b < ∟ := by
  have hFG_int_AE_hsup_e1 : ∠ e0:a:b + ∠ e1:a:b = ∟ + ∟ := by euclid_apply (helper_3_33_hFG_int_AE_hsup_e1 a b e0 e1 AE AB (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e1.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AB; assumption)) (by euclid_assumption "" (show between e0 a e1; assumption)))
  have hFG_int_AE_hne_e0 : ∠ e0:a:b ≠ ∟ := by euclid_apply (helper_3_33_hFG_int_AE_hne_e0 a b c₁ c c₂ d e0 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
  have hge : ∟ ≤ ∠ e0:a:b := not_lt.mp hpe2
  rcases lt_or_gt_of_ne hFG_int_AE_hne_e0 with h | h
  · linarith
  · linarith

end Elements.Book3
