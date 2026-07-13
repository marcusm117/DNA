import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop35.gapDiam_powac
import Book3.Prop35.gapDiam_powbd
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_gapDiam (a b c d e f : Point) (ABCD : Circle) (AC BD : Line)
  (ha : a.onCircle ABCD) (hb : b.onCircle ABCD) (hc : c.onCircle ABCD) (hd : d.onCircle ABCD)
  (hbet1 : between a e c) (hbet2 : between b e d)
  (hfc : f.isCentre ABCD)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbBD : b.onLine BD) (hdBD : d.onLine BD)
  : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)| := by
  -- power of the point E: |XE|·|EY| + |FE|² = |FX|² (= r²) for each chord, whether or not it is a diameter
  have gapDiam_powac : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─a)| * |(f─a)| := by euclid_apply (helper_3_35_gapDiam_powac a c e f ABCD AC (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)))
  have gapDiam_powbd : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by euclid_apply (helper_3_35_gapDiam_powbd b d e f ABCD BD (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)))
  have hrad : |(f─a)| = |(f─b)| := by euclid_finish
  have hrad2 : |(f─a)| * |(f─a)| = |(f─b)| * |(f─b)| := by rw [hrad]
  linarith [gapDiam_powac, gapDiam_powbd, hrad2]

end Elements.Book3
