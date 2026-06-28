import SystemE
import Book2.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_12_step1
  (d a c : Point) (CA : Line)
  (hd : d.onLine CA) (ha : a.onLine CA) (hc : c.onLine CA)
  (hassump1 : between d a c)
  : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|) := by
  have hdc : |(d─c)| = |(d─a)| + |(a─c)| := by euclid_finish
  have hda : |(d─a)| = |(a─d)| := by euclid_finish
  have hac : |(a─c)| = |(c─a)| := by euclid_finish
  have hne : d ≠ c := by euclid_finish
  have hdist : distinctPointsOnLine d c CA := ⟨hd, hc, hne⟩
  euclid_apply (proposition_4 d c a CA)
  rw [hdc, hda, hac]; ring

end Elements.Book2
