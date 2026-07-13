import SystemE
import Book1.Prop12.Main
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
import Book3.Prop35.step15_47fb
import Book3.Prop35.step15_47fd
import Book3.Prop35.step15_47fe
import Book3.Prop35.step15_ii5
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

-- "For the same reasons": the power of the point E with respect to chord BD. Same argument as for AC
-- (steps 5-14), done in one cone via a fresh perpendicular foot from the centre onto BD.
theorem helper_3_35_step15 (b d e f : Point) (ABCD : Circle) (BD : Line)
  (hb : b.onCircle ABCD) (hd : d.onCircle ABCD) (hbet2 : between b e d)
  (hfc : f.isCentre ABCD) (hbBD : b.onLine BD) (hdBD : d.onLine BD)
  (hf_bd : ¬f.onLine BD)
  : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by
  euclid_apply (proposition_12 b d f BD) as m
  euclid_apply (line_from_points f m) as FM
  have step15_47fb : |(f─b)| * |(f─b)| = |(m─b)| * |(m─b)| + |(m─f)| * |(m─f)| := by euclid_apply (helper_3_35_step15_47fb b f m BD FM (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BD; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine BD → p ≠ m → ∠ p:m:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FM; assumption)) (by euclid_assumption "" (show m.onLine FM; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)))
  have step15_47fd : |(f─d)| * |(f─d)| = |(m─d)| * |(m─d)| + |(m─f)| * |(m─f)| := by euclid_apply (helper_3_35_step15_47fd d f m BD FM (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BD; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine BD → p ≠ m → ∠ p:m:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FM; assumption)) (by euclid_assumption "" (show m.onLine FM; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)))
  have step15_47fe : |(f─e)| * |(f─e)| = |(m─e)| * |(m─e)| + |(m─f)| * |(m─f)| := by euclid_apply (helper_3_35_step15_47fe b d e f m BD FM (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BD; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine BD → p ≠ m → ∠ p:m:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FM; assumption)) (by euclid_assumption "" (show m.onLine FM; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)))
  have hbisect : |(m─b)| = |(m─d)| := by euclid_finish
  have step15_ii5 : |(b─e)| * |(e─d)| + |(m─e)| * |(m─e)| = |(m─d)| * |(m─d)| := by euclid_apply (helper_3_35_step15_ii5 b d e m BD (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BD; assumption)) (by euclid_assumption "" (show |(m─b)| = |(m─d)|; assumption)))
  have hrad : |(f─d)| = |(f─b)| := by euclid_finish
  have hrad2 : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| := by rw [hrad]
  linarith [step15_ii5, step15_47fe, step15_47fd, hrad2]

end Elements.Book3
