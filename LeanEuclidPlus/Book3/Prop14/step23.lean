import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step23
    (a c e f g : Point)
    (hstep22 : |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| = |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| ∧
                |(e─f)| * |(e─f)| = |(e─g)| * |(e─g)|) :
    |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)| := by
  obtain ⟨h1, h2⟩ := hstep22
  rw [segment_symmetric f a, segment_symmetric g c] at h1
  linarith [h1, h2]

end Elements.Book3
