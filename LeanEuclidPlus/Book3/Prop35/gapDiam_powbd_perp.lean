import SystemE
import Book1.Prop12.Main
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
import Book3.Prop35.gapDiam_bd_47fb
import Book3.Prop35.gapDiam_bd_47fd
import Book3.Prop35.gapDiam_bd_47fe
import Book3.Prop35.gapDiam_bd_ii5
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_35_gapDiam_powbd_perp (b d e f : Point) (ABCD : Circle) (BD : Line)
  (hb : b.onCircle ABCD) (hd : d.onCircle ABCD) (hbet2 : between b e d)
  (hfc : f.isCentre ABCD) (hbBD : b.onLine BD) (hdBD : d.onLine BD)
  (hf_bd : ¬f.onLine BD)
  : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by
  -- Drop the perpendicular FM from the centre F onto the chord BD, foot m.
  euclid_apply (proposition_12 b d f BD) as m
  euclid_apply (line_from_points f m) as FM
  -- Pythagoras (I.47) in the right triangles FMB, FMD, FME (right angle at the foot m).
  have gapDiam_bd_47fb : |(f─b)| * |(f─b)| = |(m─b)| * |(m─b)| + |(m─f)| * |(m─f)| := by euclid_apply (helper_3_35_gapDiam_bd_47fb b f m BD FM (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BD; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine BD → p ≠ m → ∠ p:m:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FM; assumption)) (by euclid_assumption "" (show m.onLine FM; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)))
  have gapDiam_bd_47fd : |(f─d)| * |(f─d)| = |(m─d)| * |(m─d)| + |(m─f)| * |(m─f)| := by euclid_apply (helper_3_35_gapDiam_bd_47fd d f m BD FM (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BD; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine BD → p ≠ m → ∠ p:m:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FM; assumption)) (by euclid_assumption "" (show m.onLine FM; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)))
  have gapDiam_bd_47fe : |(f─e)| * |(f─e)| = |(m─e)| * |(m─e)| + |(m─f)| * |(m─f)| := by euclid_apply (helper_3_35_gapDiam_bd_47fe b d e f m BD FM (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BD; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine BD → p ≠ m → ∠ p:m:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FM; assumption)) (by euclid_assumption "" (show m.onLine FM; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)))
  -- |fb|=|fd| (equal radii) with the two Pythagoras identities forces |mb|=|md|: m is the midpoint.
  have hbisect : |(m─b)| = |(m─d)| := by euclid_finish
  -- II.5 on BD cut equally at m and unequally at e.
  have gapDiam_bd_ii5 : |(b─e)| * |(e─d)| + |(m─e)| * |(m─e)| = |(m─d)| * |(m─d)| := by euclid_apply (helper_3_35_gapDiam_bd_ii5 b d e m BD (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BD; assumption)) (by euclid_assumption "" (show |(m─b)| = |(m─d)|; assumption)))
  have hrad : |(f─d)| = |(f─b)| := by euclid_finish
  have hrad2 : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| := by rw [hrad]
  linarith [gapDiam_bd_ii5, gapDiam_bd_47fe, gapDiam_bd_47fd, hrad2]

end Elements.Book3
