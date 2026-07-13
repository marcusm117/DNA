import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_step15_47fe (b d e f m : Point) (BD FM : Line)
  (hbet2 : between b e d) (hbBD : b.onLine BD) (hdBD : d.onLine BD)
  (hmBD : m.onLine BD) (hperp : ∀ (p : Point), p.onLine BD → p ≠ m → ∠ p:m:f = ∟)
  (hfFM : f.onLine FM) (hmFM : m.onLine FM) (hf_bd : ¬f.onLine BD)
  : |(f─e)| * |(f─e)| = |(m─e)| * |(m─e)| + |(m─f)| * |(m─f)| := by
  by_cases hem : e = m
  · subst hem
    euclid_finish
  · have heBD : e.onLine BD := by euclid_finish
    euclid_apply (line_from_points f e) as FE
    have heoffFM : ¬e.onLine FM :=
      offLine_of_two_points e m f BD FM heBD hmBD hem hmFM hfFM hf_bd
    have hmoffFE : ¬m.onLine FE :=
      offLine_of_two_points m e f BD FE hmBD heBD (Ne.symm hem) (by euclid_finish) (by euclid_finish) hf_bd
    have hang : ∠ f:m:e = ∟ := by euclid_finish
    have htri : formTriangle m f e FM FE BD := by euclid_finish
    euclid_apply (proposition_47 m f e FM FE BD)
    euclid_finish

end Elements.Book3
