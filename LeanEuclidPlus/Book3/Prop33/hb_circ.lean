import SystemE
import Book3.Prop33.hFG_int_AE_he0off
import Book3.Prop33.hb_circ_gab
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- b is on the circle (centre g, radius ga): ga = gb (SAS, hb_circ_gab), and a is on the circle.
-- (g is off AB — else g ∈ AE ∩ AB = {a}, contradicting g ≠ a; uses e0 ∉ AB so AE ≠ AB.)
theorem helper_3_33_hb_circ
    (a b c₁ c c₂ d e0 f g g0 : Point) (AB AD AE FG GB : Line) (α : Circle)
    (hne : a ≠ b) (hc1c : c₁ ≠ c) (hcc2 : c ≠ c₂)
    (hpos : 0 < ∠ c₁:c:c₂)
    (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (haab : a.onLine AB) (hbab : b.onLine AB)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0offAD : ¬ e0.onLine AD)
    (hperp_e : ∠ d:a:e0 = ∟) (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hadd : d ≠ a)
    (haAE : a.onLine AE) (he0AE : e0.onLine AE) (hgAE : g.onLine AE)
    (hafb : between a f b) (haffb : |(a─f)| = |(f─b)|)
    (hg0off : ¬ g0.onLine AB) (hperp_g : ∠ a:f:g0 = ∟)
    (hfFG : f.onLine FG) (hg0FG : g0.onLine FG) (hgFG : g.onLine FG)
    (hgcen : g.isCentre α) (hacirc : a.onCircle α) (hga : g ≠ a) (hgb : g ≠ b)
    (hgGB : g.onLine GB) (hbGB : b.onLine GB) :
    b.onCircle α := by
  have hFG_int_AE_he0off : ¬ e0.onLine AB := by euclid_apply (helper_3_33_hFG_int_AE_he0off a b c₁ c c₂ d e0 AD AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
  have hgoffAB : ¬ g.onLine AB := by euclid_finish
  have hb_circ_gab : |(g─a)| = |(g─b)| := by euclid_apply (helper_3_33_hb_circ_gab a b f g g0 AB FG GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)) (by euclid_assumption "" (show ¬ g.onLine AB; assumption)))
  euclid_finish

end Elements.Book3
