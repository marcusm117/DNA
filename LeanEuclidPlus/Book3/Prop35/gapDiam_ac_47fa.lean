import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_gapDiam_ac_47fa (a f m : Point) (AC FM : Line)
  (haAC : a.onLine AC)
  (hmAC : m.onLine AC) (hperp : ∀ (p : Point), p.onLine AC → p ≠ m → ∠ p:m:f = ∟)
  (hfFM : f.onLine FM) (hmFM : m.onLine FM) (hf_ac : ¬f.onLine AC)
  : |(f─a)| * |(f─a)| = |(m─a)| * |(m─a)| + |(m─f)| * |(m─f)| := by
  by_cases ham : a = m
  · subst ham
    euclid_finish
  · euclid_apply (line_from_points f a) as FA
    have haoffFM : ¬a.onLine FM :=
      offLine_of_two_points a m f AC FM haAC hmAC ham hmFM hfFM hf_ac
    have hmoffFA : ¬m.onLine FA :=
      offLine_of_two_points m a f AC FA hmAC haAC (Ne.symm ham) (by euclid_finish) (by euclid_finish) hf_ac
    have hang : ∠ f:m:a = ∟ := by euclid_finish
    have htri : formTriangle m f a FM FA AC := by euclid_finish
    euclid_apply (proposition_47 m f a FM FA AC)
    euclid_finish

end Elements.Book3
