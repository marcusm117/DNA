import SystemE
import Book3.Prop35.gapDiam_powac_diam
import Book3.Prop35.gapDiam_powac_perp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_gapDiam_powac (a c e f : Point) (ABCD : Circle) (AC : Line)
  (ha : a.onCircle ABCD) (hc : c.onCircle ABCD) (hbet1 : between a e c)
  (hfc : f.isCentre ABCD) (haAC : a.onLine AC) (hcAC : c.onLine AC)
  : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─a)| * |(f─a)| := by
  by_cases hf_ac : f.onLine AC
  · -- $AC$ passes through the centre: $F$ itself is the midpoint of the chord.
    have gapDiam_powac_diam : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─a)| * |(f─a)| := by euclid_apply (helper_3_35_gapDiam_powac_diam a c e f ABCD AC (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)))
    exact gapDiam_powac_diam
  · -- $AC$ not through the centre: drop the perpendicular from $F$ to $AC$.
    have gapDiam_powac_perp : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─a)| * |(f─a)| := by euclid_apply (helper_3_35_gapDiam_powac_perp a c e f ABCD AC (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)))
    exact gapDiam_powac_perp

end Elements.Book3
