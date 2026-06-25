import SystemE

namespace Elements.Book1

/- 1.6.11: thus AB = AC — from ¬(AB ≠ AC) by double-negation (by_contra). -/
set_option systemE.solverTime 30 in
theorem helper_1_6_step11 (a b c : Point) (habsurd : ¬ (|(a─b)| ≠ |(a─c)|)) :
    |(a─b)| = |(a─c)| := by
  by_contra h
  exact habsurd h

end Elements.Book1
