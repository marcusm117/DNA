import SystemE
import Book1.Prop12.Main
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
import Book3.Prop35.gapDiam_ac_47fa
import Book3.Prop35.gapDiam_ac_47fc
import Book3.Prop35.gapDiam_ac_47fe
import Book3.Prop35.gapDiam_ac_ii5
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_35_gapDiam_powac_perp (a c e f : Point) (ABCD : Circle) (AC : Line)
  (ha : a.onCircle ABCD) (hc : c.onCircle ABCD) (hbet1 : between a e c)
  (hfc : f.isCentre ABCD) (haAC : a.onLine AC) (hcAC : c.onLine AC)
  (hf_ac : ¬f.onLine AC)
  : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─a)| * |(f─a)| := by
  -- Drop the perpendicular FM from the centre F onto the chord AC, foot m.
  euclid_apply (proposition_12 a c f AC) as m
  euclid_apply (line_from_points f m) as FM
  -- Pythagoras (I.47) in the right triangles FMA, FMC, FME (right angle at the foot m).
  have gapDiam_ac_47fa : |(f─a)| * |(f─a)| = |(m─a)| * |(m─a)| + |(m─f)| * |(m─f)| := by euclid_apply (helper_3_35_gapDiam_ac_47fa a f m AC FM (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show m.onLine AC; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine AC → p ≠ m → ∠ p:m:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FM; assumption)) (by euclid_assumption "" (show m.onLine FM; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)))
  have gapDiam_ac_47fc : |(f─c)| * |(f─c)| = |(m─c)| * |(m─c)| + |(m─f)| * |(m─f)| := by euclid_apply (helper_3_35_gapDiam_ac_47fc c f m AC FM (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show m.onLine AC; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine AC → p ≠ m → ∠ p:m:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FM; assumption)) (by euclid_assumption "" (show m.onLine FM; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)))
  have gapDiam_ac_47fe : |(f─e)| * |(f─e)| = |(m─e)| * |(m─e)| + |(m─f)| * |(m─f)| := by euclid_apply (helper_3_35_gapDiam_ac_47fe a c e f m ABCD AC FM (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show m.onLine AC; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine AC → p ≠ m → ∠ p:m:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FM; assumption)) (by euclid_assumption "" (show m.onLine FM; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)))
  -- |fa|=|fc| (equal radii) with the two Pythagoras identities forces |ma|=|mc|: m is the midpoint.
  have hbisect : |(m─a)| = |(m─c)| := by euclid_finish
  -- II.5 on AC cut equally at m and unequally at e.
  have gapDiam_ac_ii5 : |(a─e)| * |(e─c)| + |(m─e)| * |(m─e)| = |(m─c)| * |(m─c)| := by euclid_apply (helper_3_35_gapDiam_ac_ii5 a c e m AC (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show m.onLine AC; assumption)) (by euclid_assumption "" (show |(m─a)| = |(m─c)|; assumption)))
  have hrad : |(f─c)| = |(f─a)| := by euclid_finish
  have hrad2 : |(f─c)| * |(f─c)| = |(f─a)| * |(f─a)| := by rw [hrad]
  linarith [gapDiam_ac_ii5, gapDiam_ac_47fe, gapDiam_ac_47fc, hrad2]

end Elements.Book3
