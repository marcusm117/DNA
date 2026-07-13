import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_step10 (a c e f g : Point) (AC FE : Line)
  (hbet_aec : between a e c) (haAC : a.onLine AC) (hcAC : c.onLine AC) (hgAC : g.onLine AC)
  (hgperp : ∀ (p : Point), p.onLine AC → p ≠ g → ∠ p:g:f = ∟)
  (hfFE : f.onLine FE) (heFE : e.onLine FE) (hf_ac : ¬f.onLine AC)
  : |(f─e)| * |(f─e)| = |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| := by
  have heAC : e.onLine AC := by euclid_finish
  by_cases heg : e = g
  · subst heg
    euclid_finish
  · euclid_apply (line_from_points f g) as FG
    have heoffFG : ¬e.onLine FG :=
      offLine_of_two_points e g f AC FG heAC hgAC heg (by euclid_finish) (by euclid_finish) hf_ac
    have hgoffFE : ¬g.onLine FE :=
      offLine_of_two_points g e f AC FE hgAC heAC (Ne.symm heg) heFE hfFE hf_ac
    have hang : ∠ f:g:e = ∟ := by euclid_finish
    have htri : formTriangle g f e FG FE AC := by euclid_finish
    euclid_apply (proposition_47 g f e FG FE AC)
    euclid_finish

end Elements.Book3
