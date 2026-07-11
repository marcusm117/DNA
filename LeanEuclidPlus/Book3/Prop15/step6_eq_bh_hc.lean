import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- |b─h| = |h─c|: both Pythagorean equations have the same RHS (|e─b|²),
-- so |b─h|² = |h─c|² → (|b─h| - |h─c|)(|b─h| + |h─c|) = 0 → |b─h| = |h─c|.
set_option systemE.solverTime 30 in
theorem helper_3_15_step6_eq_bh_hc
    (b h c e : Point)
    (h_pb : |(b─h)| * |(b─h)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)|)
    (h_pc : |(h─c)| * |(h─c)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)|) :
    |(b─h)| = |(h─c)| := by
  have h_sq : |(b─h)| * |(b─h)| = |(h─c)| * |(h─c)| := by nlinarith [h_pb, h_pc]
  have h_fact : (|(b─h)| - |(h─c)|) * (|(b─h)| + |(h─c)|) = 0 := by nlinarith [h_sq]
  rcases mul_eq_zero.mp h_fact with h1 | h2
  · linarith
  · have := segment_gte_zero (b─h); have := segment_gte_zero (h─c); linarith

end Elements.Book3
