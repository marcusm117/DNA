import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagoras (I.47) for the right triangle a-f-e (right angle at f).
theorem helper_3_14_step10
    (a b e f : Point) (ABDC : Circle) (AB : Line)
    (ha : a.onCircle ABDC) (hcen : e.isCentre ABDC)
    (haAB : a.onLine AB) (hfAB : f.onLine AB)
    (hafb : between a f b) (hef : e ≠ f)
    (hassump1 : ∠ a:f:e = ∟) :
    |(a─f)| * |(a─f)| + |(e─f)| * |(e─f)| = |(a─e)| * |(a─e)| := by
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points f e) as FE
  have h_e_off : ¬ e.onLine AB := by euclid_finish
  have htri : formTriangle f a e AB AE FE := by euclid_finish
  have hp : |(a─e)| * |(a─e)| = |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| := by
    euclid_apply (Elements.Book1.proposition_47 f a e AB AE FE)
    euclid_finish
  have hsymm : |(e─f)| = |(f─e)| := segment_symmetric e f
  rw [hsymm]; linarith [hp]

end Elements.Book3
