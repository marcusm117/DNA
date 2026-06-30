import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step7 (2.13.7): "So the square on AC alone is less than the squares on CB and BA by
-- twice rect(CB,BD)." This is step6 with the two sides swapped (identical terms).
theorem helper_2_13_step7
  (a b c d : Point)
  (hstep6 : |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| = |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|))
  : |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|) = |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| := by
  linarith [hstep6]

end Elements.Book2
