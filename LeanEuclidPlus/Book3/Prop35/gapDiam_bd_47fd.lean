import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_gapDiam_bd_47fd (d f m : Point) (BD FM : Line)
  (hdBD : d.onLine BD)
  (hmBD : m.onLine BD) (hperp : ∀ (p : Point), p.onLine BD → p ≠ m → ∠ p:m:f = ∟)
  (hfFM : f.onLine FM) (hmFM : m.onLine FM) (hf_bd : ¬f.onLine BD)
  : |(f─d)| * |(f─d)| = |(m─d)| * |(m─d)| + |(m─f)| * |(m─f)| := by
  by_cases hdm : d = m
  · subst hdm
    euclid_finish
  · euclid_apply (line_from_points f d) as FD
    have hdoffFM : ¬d.onLine FM :=
      offLine_of_two_points d m f BD FM hdBD hmBD hdm hmFM hfFM hf_bd
    have hmoffFD : ¬m.onLine FD :=
      offLine_of_two_points m d f BD FD hmBD hdBD (Ne.symm hdm) (by euclid_finish) (by euclid_finish) hf_bd
    have hang : ∠ f:m:d = ∟ := by euclid_finish
    have htri : formTriangle m f d FM FD BD := by euclid_finish
    euclid_apply (proposition_47 m f d FM FD BD)
    euclid_finish

end Elements.Book3
