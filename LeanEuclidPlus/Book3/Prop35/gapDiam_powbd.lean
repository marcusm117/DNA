import SystemE
import Book3.Prop35.gapDiam_powbd_diam
import Book3.Prop35.gapDiam_powbd_perp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_gapDiam_powbd (b d e f : Point) (ABCD : Circle) (BD : Line)
  (hb : b.onCircle ABCD) (hd : d.onCircle ABCD) (hbet2 : between b e d)
  (hfc : f.isCentre ABCD) (hbBD : b.onLine BD) (hdBD : d.onLine BD)
  : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by
  by_cases hf_bd : f.onLine BD
  · -- $BD$ passes through the centre: $F$ itself is the midpoint of the chord.
    have gapDiam_powbd_diam : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by euclid_apply (helper_3_35_gapDiam_powbd_diam b d e f ABCD BD (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show f.onLine BD; assumption)))
    exact gapDiam_powbd_diam
  · -- $BD$ not through the centre: drop the perpendicular from $F$ to $BD$.
    have gapDiam_powbd_perp : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by euclid_apply (helper_3_35_gapDiam_powbd_perp b d e f ABCD BD (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)))
    exact gapDiam_powbd_perp

end Elements.Book3
