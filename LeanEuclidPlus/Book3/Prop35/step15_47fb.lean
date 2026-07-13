import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_step15_47fb (b f m : Point) (BD FM : Line)
  (hbBD : b.onLine BD)
  (hmBD : m.onLine BD) (hperp : ∀ (p : Point), p.onLine BD → p ≠ m → ∠ p:m:f = ∟)
  (hfFM : f.onLine FM) (hmFM : m.onLine FM) (hf_bd : ¬f.onLine BD)
  : |(f─b)| * |(f─b)| = |(m─b)| * |(m─b)| + |(m─f)| * |(m─f)| := by
  by_cases hbm : b = m
  · subst hbm
    euclid_finish
  · euclid_apply (line_from_points f b) as FB
    have hboffFM : ¬b.onLine FM :=
      offLine_of_two_points b m f BD FM hbBD hmBD hbm hmFM hfFM hf_bd
    have hmoffFB : ¬m.onLine FB :=
      offLine_of_two_points m b f BD FB hmBD hbBD (Ne.symm hbm) (by euclid_finish) (by euclid_finish) hf_bd
    have hang : ∠ f:m:b = ∟ := by euclid_finish
    have htri : formTriangle m f b FM FB BD := by euclid_finish
    euclid_apply (proposition_47 m f b FM FB BD)
    euclid_finish

end Elements.Book3
