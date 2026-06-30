import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop11.step8_pyth
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step12
    (a b c e : Point) (AB AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbet_aec : between a e c)
    -- @assumption: "the angle at $A$ (is) a right-angle"
    (hang_bac : ∠ b:a:c = ∟) :
    |(b─a)| * |(b─a)| + |(a─e)| * |(a─e)| = |(e─b)| * |(e─b)| := by
  -- Pythagoras on right triangle a-e-b [Prop.~1.47] (reuses step8_pyth).
  have step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by euclid_apply (helper_2_11_step8_pyth a b c e AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)))
  have hba : |(b─a)| = |(a─b)| := (segment_symmetric a b).symm
  rw [hba]
  linarith [step8_pyth]

end Elements.Book2
