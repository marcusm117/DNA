import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step22
    (a c e f g : Point)
    (hstep20 : |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| = |(a─e)| * |(a─e)|)
    (hstep21 : |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| = |(e─c)| * |(e─c)|)
    (hstep19 : |(a─e)| * |(a─e)| = |(e─c)| * |(e─c)|)
    (hassump1 : |(e─f)| = |(e─g)|) :
    |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| = |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| ∧
                |(e─f)| * |(e─f)| = |(e─g)| * |(e─g)| := by
  refine ⟨?_, ?_⟩
  · linarith [hstep20, hstep21, hstep19]
  · rw [hassump1]

end Elements.Book3
