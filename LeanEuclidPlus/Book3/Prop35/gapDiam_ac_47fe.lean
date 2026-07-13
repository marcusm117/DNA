import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_gapDiam_ac_47fe (a c e f m : Point) (ABCD : Circle) (AC FM : Line)
  (hbet1 : between a e c) (haAC : a.onLine AC) (hcAC : c.onLine AC)
  (hmAC : m.onLine AC) (hperp : ∀ (p : Point), p.onLine AC → p ≠ m → ∠ p:m:f = ∟)
  (hfFM : f.onLine FM) (hmFM : m.onLine FM) (hf_ac : ¬f.onLine AC)
  : |(f─e)| * |(f─e)| = |(m─e)| * |(m─e)| + |(m─f)| * |(m─f)| := by
  by_cases hem : e = m
  · -- E coincides with the perpendicular foot: the identity is trivial (|me| = 0, |mf| = |fe|).
    subst hem
    euclid_finish
  · have heAC : e.onLine AC := by euclid_finish
    euclid_apply (line_from_points f e) as FE
    -- off-line facts (instant term lemmas) to assemble the right triangle m f e (side m-e is AC itself)
    have heoffFM : ¬e.onLine FM :=
      offLine_of_two_points e m f AC FM heAC hmAC hem hmFM hfFM hf_ac
    have hmoffFE : ¬m.onLine FE :=
      offLine_of_two_points m e f AC FE hmAC heAC (Ne.symm hem) (by euclid_finish) (by euclid_finish) hf_ac
    have hang : ∠ f:m:e = ∟ := by euclid_finish
    have htri : formTriangle m f e FM FE AC := by euclid_finish
    euclid_apply (proposition_47 m f e FM FE AC)
    euclid_finish

end Elements.Book3
