import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_step11 (c f g : Point) (AC FC : Line)
  (hcAC : c.onLine AC) (hgAC : g.onLine AC)
  (hgperp : ∀ (p : Point), p.onLine AC → p ≠ g → ∠ p:g:f = ∟)
  (hfFC : f.onLine FC) (hcFC : c.onLine FC) (hf_ac : ¬f.onLine AC)
  : |(f─c)| * |(f─c)| = |(c─g)| * |(c─g)| + |(g─f)| * |(g─f)| := by
  by_cases hcg : c = g
  · subst hcg
    euclid_finish
  · euclid_apply (line_from_points f g) as FG
    have hcoffFG : ¬c.onLine FG :=
      offLine_of_two_points c g f AC FG hcAC hgAC hcg (by euclid_finish) (by euclid_finish) hf_ac
    have hgoffFC : ¬g.onLine FC :=
      offLine_of_two_points g c f AC FC hgAC hcAC (Ne.symm hcg) hcFC hfFC hf_ac
    have hang : ∠ f:g:c = ∟ := by euclid_finish
    have htri : formTriangle g f c FG FC AC := by euclid_finish
    euclid_apply (proposition_47 g f c FG FC AC)
    euclid_finish

end Elements.Book3
