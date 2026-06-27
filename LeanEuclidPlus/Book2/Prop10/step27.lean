import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.27: square on EA = double the square on AC. From step26 (|e─a|² = |e─c|² + |c─a|²) and step25
   (|e─c|² + |c─a|² = 2|c─a|²); the |c─a| ↔ |a─c| orientation is segment symmetry. Pure linarith. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step27
  (a c e : Point)
  (hstep26 : |(e─a)| * |(e─a)| = |(e─c)| * |(e─c)| + |(c─a)| * |(c─a)|)
  (hstep25 : |(e─c)| * |(e─c)| + |(c─a)| * |(c─a)| = 2 * (|(c─a)| * |(c─a)|)) :
  |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|) := by
  have hca2 : |(c─a)| * |(c─a)| = |(a─c)| * |(a─c)| := by rw [segment_symmetric c a]
  linarith

end Elements.Book2
