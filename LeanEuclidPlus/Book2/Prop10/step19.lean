import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.19: ∠DGB = ∠DBG. Both are half a right-angle (step18: ∠d:g:b = ∟/2, step16: ∠d:b:g = ∟/2),
   hence equal. Pure arithmetic over the two half-angle facts — no geometry, no SMT. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step19
  (d b g : Point)
  (hstep16 : ∠ d:b:g = ∟ / 2)
  (hstep18 : ∠ d:g:b = ∟ / 2) :
  ∠ d:g:b = ∠ d:b:g := by
  linarith [hstep16, hstep18]

end Elements.Book2
