import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_40 : ∀  (a b c d e : Point) (AB BC AC CD DE AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d c e CD BC DE ∧ a.sameSide d BC ∧ b ≠ e ∧ |(b─c)| = |(c─e)| ∧
  distinctPointsOnLine a d AD ∧ (Triangle.area △ a:b:c = Triangle.area △ d:c:e) →
  ¬(AD.intersectsLine BC) := by
  sorry

end Elements.Book1
