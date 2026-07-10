import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step25
    (ABC : Circle) (m k d b0 g : Point)
    (hm : m.isCentre ABC)
    (hb0_circ : b0.onCircle ABC)
    (hbet_dgm : between d g m)
    (hb0_ang : ∠ d:m:b0 = ∠ k:m:d) :
    ∠ k:m:d = ∠ b0:m:d := by
  have hne_dm : d ≠ m := by euclid_finish
  have hne_b0m : b0 ≠ m := by
    intro h
    exact absurd (h ▸ hb0_circ) (by euclid_finish)
  have hsym : ∠ d:m:b0 = ∠ b0:m:d := angle_symm d m b0 ⟨hne_dm, hne_b0m.symm⟩
  linarith

end Elements.Book3
