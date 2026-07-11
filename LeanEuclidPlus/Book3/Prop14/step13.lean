import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step13
    (a c e f g : Point)
    (hstep12 : |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| = |(c─g)| * |(c─g)| + |(g─e)| * |(g─e)| ∧
                |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)|) :
    |(f─e)| * |(f─e)| = |(e─g)| * |(e─g)| := by
  obtain ⟨h1, h2⟩ := hstep12
  rw [segment_symmetric g e] at h1
  linarith [h1, h2]

end Elements.Book3
