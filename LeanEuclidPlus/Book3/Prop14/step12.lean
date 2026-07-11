import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step12
    (a c e f g : Point)
    (hstep10 : |(a─f)| * |(a─f)| + |(e─f)| * |(e─f)| = |(a─e)| * |(a─e)|)
    (hstep11 : |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| = |(e─c)| * |(e─c)|)
    (hstep9 : |(a─e)| * |(a─e)| = |(e─c)| * |(e─c)|)
    (hassump1 : |(a─f)| = |(c─g)|) :
    |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| = |(c─g)| * |(c─g)| + |(g─e)| * |(g─e)| ∧
                |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)| := by
  refine ⟨?_, ?_⟩
  · rw [segment_symmetric e f] at hstep10
    rw [segment_symmetric e g, segment_symmetric g c] at hstep11
    linarith [hstep10, hstep11, hstep9]
  · rw [hassump1]

end Elements.Book3
