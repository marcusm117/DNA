import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/- 1.6.11: thus AB = AC — from ¬(AB ≠ AC) by double-negation (by_contra). -/
theorem helper_1_6_step11 (a b c : Point) (habsurd : ¬ (|(a─b)| ≠ |(a─c)|)) :
    |(a─b)| = |(a─c)| := by
  by_contra h
  exact habsurd h

end Elements.Book1
