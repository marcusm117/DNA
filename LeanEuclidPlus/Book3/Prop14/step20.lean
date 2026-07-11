import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagoras (I.47) for the right triangle a-f-e (right angle at f).
theorem helper_3_14_step20
    (a b e f : Point) (ABDC : Circle) (AB : Line)
    (ha : a.onCircle ABDC) (hcen : e.isCentre ABDC)
    (haAB : a.onLine AB) (hfAB : f.onLine AB)
    (hafb : between a f b) (hef : e ≠ f)
    (hfangle : ∠ a:f:e = ∟) :
    |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| = |(a─e)| * |(a─e)| := by
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points f e) as FE
  have h_e_off : ¬ e.onLine AB := by euclid_finish
  have htri : formTriangle f a e AB AE FE := by euclid_finish
  have hp : |(a─e)| * |(a─e)| = |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| := by
    euclid_apply (Elements.Book1.proposition_47 f a e AB AE FE)
    euclid_finish
  have h1 : |(e─f)| = |(f─e)| := segment_symmetric e f
  have h2 : |(f─a)| = |(a─f)| := segment_symmetric f a
  rw [h1, h2]; linarith [hp]

end Elements.Book3
