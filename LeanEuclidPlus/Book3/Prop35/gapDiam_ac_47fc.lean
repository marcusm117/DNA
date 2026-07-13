import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_gapDiam_ac_47fc (c f m : Point) (AC FM : Line)
  (hcAC : c.onLine AC)
  (hmAC : m.onLine AC) (hperp : ∀ (p : Point), p.onLine AC → p ≠ m → ∠ p:m:f = ∟)
  (hfFM : f.onLine FM) (hmFM : m.onLine FM) (hf_ac : ¬f.onLine AC)
  : |(f─c)| * |(f─c)| = |(m─c)| * |(m─c)| + |(m─f)| * |(m─f)| := by
  by_cases hcm : c = m
  · subst hcm
    euclid_finish
  · euclid_apply (line_from_points f c) as FC
    have hcoffFM : ¬c.onLine FM :=
      offLine_of_two_points c m f AC FM hcAC hmAC hcm hmFM hfFM hf_ac
    have hmoffFC : ¬m.onLine FC :=
      offLine_of_two_points m c f AC FC hmAC hcAC (Ne.symm hcm) (by euclid_finish) (by euclid_finish) hf_ac
    have hang : ∠ f:m:c = ∟ := by euclid_finish
    have htri : formTriangle m f c FM FC AC := by euclid_finish
    euclid_apply (proposition_47 m f c FM FC AC)
    euclid_finish

end Elements.Book3
