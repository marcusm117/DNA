import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_step5_47fa (a f g : Point) (AC FG : Line)
  (haAC : a.onLine AC) (hgAC : g.onLine AC)
  (hgperp : ∀ (p : Point), p.onLine AC → p ≠ g → ∠ p:g:f = ∟)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG) (hf_ac : ¬f.onLine AC)
  : |(f─a)| * |(f─a)| = |(g─a)| * |(g─a)| + |(g─f)| * |(g─f)| := by
  by_cases hag : a = g
  · subst hag
    euclid_finish
  · euclid_apply (line_from_points f a) as FA
    have haoffFG : ¬a.onLine FG :=
      offLine_of_two_points a g f AC FG haAC hgAC hag hgFG hfFG hf_ac
    have hgoffFA : ¬g.onLine FA :=
      offLine_of_two_points g a f AC FA hgAC haAC (Ne.symm hag) (by euclid_finish) (by euclid_finish) hf_ac
    have hang : ∠ f:g:a = ∟ := by euclid_finish
    have htri : formTriangle g f a FG FA AC := by euclid_finish
    euclid_apply (proposition_47 g f a FG FA AC)
    euclid_finish

end Elements.Book3
