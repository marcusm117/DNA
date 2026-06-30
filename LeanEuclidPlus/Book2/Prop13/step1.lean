import SystemE
import Book2.Prop07.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step1 (2.13.1): CB cut at D ⟹ squares on CB and BD = twice rect(CB,BD) + square on DC
-- [Prop.~2.7]. proposition_7 instantiated at (c,b,d,BC) has conclusion = this claim exactly;
-- we just discharge its antecedent (distinctPointsOnLine c b BC ∧ between c d b).
theorem helper_2_13_step1
  (c b d : Point) (BC : Line)
  (hc : c.onLine BC) (hb : b.onLine BC)
  (hassump1 : between b d c)
  : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| = 2 * (|(c─b)| * |(b─d)|) + |(d─c)| * |(d─c)| := by
  have hne : c ≠ b := by euclid_finish
  have hdist : distinctPointsOnLine c b BC := ⟨hc, hb, hne⟩
  have hcd : between c d b := (between_symm b d c hassump1).1
  euclid_apply (proposition_7 c b d BC)
  assumption

end Elements.Book2
