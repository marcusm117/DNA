import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step25
    (a b c d f g : Point)
    (hstep24 : |(a─f)| = |(c─g)|)
    (hassump1 : |(a─b)| = |(a─f)| + |(a─f)| ∧ |(c─d)| = |(c─g)| + |(c─g)|) :
    |(a─b)| = |(c─d)| := by
  obtain ⟨h1, h2⟩ := hassump1
  linarith [h1, h2, hstep24]

end Elements.Book3
