import SystemE
import Book2.Prop04.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_12_step1
  (a c d : Point) (CA : Line)
  (hd : d.onLine CA) (hc : c.onLine CA)
  (hbet : between d a c)
  : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_apply (proposition_4 d c a CA)
  have hda : |(d─a)| = |(a─d)| := by euclid_finish
  have hac : |(a─c)| = |(c─a)| := by euclid_finish
  linarith [hda, hac]

end Elements.Book2
