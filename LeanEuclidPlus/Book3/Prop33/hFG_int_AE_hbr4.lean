import SystemE
import Book3.Prop33.hFG_int_AE_hle_e1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Post-5 branch: e1 (AE extended past a) is the acute rep (hFG_int_AE_hle_e1), and g0 is on the opposite
-- side of AB from e1; extend FG past f to g0' (on e1's side); ∠a:f:g0' = ∟ still.
theorem helper_3_33_hFG_int_AE_hbr4
    (a b c₁ c c₂ d e0 e1 f g0 : Point) (AB AD AE FG : Line)
    (haae : a.onLine AE) (he0ae : e0.onLine AE) (he1ae : e1.onLine AE)
    (he1 : between e0 a e1) (he1off : ¬ e1.onLine AB)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hadd : d ≠ a) (he0off : ¬ e0.onLine AD) (hperp_e : ∠ d:a:e0 = ∟)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (he0offAB : ¬ e0.onLine AB)
    (hfb : f.onLine AB) (hafb : between a f b)
    (hperp_g : ∠ a:f:g0 = ∟)
    (hffg : f.onLine FG) (hg0fg : g0.onLine FG) (hg0off : ¬ g0.onLine AB)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (hpe2 : ¬ ∠ e0:a:b < ∟) (hqs : ¬ e1.sameSide g0 AB) (hafne : a ≠ f) :
    FG.intersectsLine AE := by
  have hFG_int_AE_hle_e1 : ∠ e1:a:b < ∟ := by euclid_apply (helper_3_33_hFG_int_AE_hle_e1 a b c₁ c c₂ d e0 e1 AD AE AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e1.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AB; assumption)) (by euclid_assumption "" (show between e0 a e1; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show ¬ ∠ e0:a:b < ∟; assumption)))
  euclid_apply (extend_point FG g0 f) as g0'
  have hss : e1.sameSide g0' AB := by euclid_finish
  have hsum : ∠ e1:a:f + ∠ a:f:g0' < ∟ + ∟ := by euclid_finish
  have haoffFG : ¬ a.onLine FG := by euclid_finish
  euclid_apply (lines_intersect e1 a f g0' AE AB FG) as gg
  have hfgne : FG ≠ AE := fun h => haoffFG (h ▸ haae)
  euclid_apply (intersection_lines_common_point gg FG AE)
  assumption

end Elements.Book3
