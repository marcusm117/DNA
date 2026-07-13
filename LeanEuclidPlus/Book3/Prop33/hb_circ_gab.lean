import SystemE
import Book1.Prop04.Main
import Book3.Prop33.hb_circ_gab_tri1
import Book3.Prop33.hb_circ_gab_tri2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

-- SAS: triangles f-a-g and f-b-g are congruent (fa = fb, fg common, ∠afg = ∠bfg = ∟), so ga = gb.
theorem helper_3_33_hb_circ_gab
    (a b f g g0 : Point) (AB FG GB : Line)
    (haab : a.onLine AB) (hbab : b.onLine AB) (hafb : between a f b) (haffb : |(a─f)| = |(f─b)|)
    (hfFG : f.onLine FG) (hg0FG : g0.onLine FG) (hg0off : ¬ g0.onLine AB) (hperp_g : ∠ a:f:g0 = ∟)
    (hgFG : g.onLine FG) (hgGB : g.onLine GB) (hbGB : b.onLine GB)
    (hga : g ≠ a) (hgb : g ≠ b) (hgoffAB : ¬ g.onLine AB) :
    |(g─a)| = |(g─b)| := by
  euclid_apply (line_from_points a g) as AG
  have hafg : ∠ a:f:g = ∟ := by euclid_finish
  have hbfg : ∠ b:f:g = ∟ := by euclid_finish
  have haoffFG : ¬ a.onLine FG := by euclid_finish
  have hboffFG : ¬ b.onLine FG := by euclid_finish
  have hb_circ_gab_tri1 : formTriangle f a g AB AG FG := by euclid_apply (helper_3_33_hb_circ_gab_tri1 a b f g g0 AB FG AG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)) (by euclid_assumption "" (show ¬ g.onLine AB; assumption)) (by euclid_assumption "" (show ¬ a.onLine FG; assumption)))
  have hb_circ_gab_tri2 : formTriangle f b g AB GB FG := by euclid_apply (helper_3_33_hb_circ_gab_tri2 a b f g g0 AB FG GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)) (by euclid_assumption "" (show ¬ g.onLine AB; assumption)) (by euclid_assumption "" (show ¬ b.onLine FG; assumption)))
  euclid_apply (proposition_4 f a g f b g AB AG FG AB GB FG)
  euclid_finish

end Elements.Book3
