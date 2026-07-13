import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_step5_47fc (c f g : Point) (AC FG : Line)
  (hcAC : c.onLine AC) (hgAC : g.onLine AC)
  (hgperp : ∀ (p : Point), p.onLine AC → p ≠ g → ∠ p:g:f = ∟)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG) (hf_ac : ¬f.onLine AC)
  : |(f─c)| * |(f─c)| = |(g─c)| * |(g─c)| + |(g─f)| * |(g─f)| := by
  by_cases hcg : c = g
  · subst hcg
    euclid_finish
  · euclid_apply (line_from_points f c) as FC2
    have hcoffFG : ¬c.onLine FG :=
      offLine_of_two_points c g f AC FG hcAC hgAC hcg hgFG hfFG hf_ac
    have hgoffFC : ¬g.onLine FC2 :=
      offLine_of_two_points g c f AC FC2 hgAC hcAC (Ne.symm hcg) (by euclid_finish) (by euclid_finish) hf_ac
    have hang : ∠ f:g:c = ∟ := by euclid_finish
    have htri : formTriangle g f c FG FC2 AC := by euclid_finish
    euclid_apply (proposition_47 g f c FG FC2 AC)
    euclid_finish

end Elements.Book3
