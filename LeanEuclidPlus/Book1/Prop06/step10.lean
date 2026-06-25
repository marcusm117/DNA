import SystemE

namespace Elements.Book1

/- 1.6.10: AB is not unequal to AC — directly the by-contradiction hypothesis habsurd. -/
set_option systemE.solverTime 30 in
theorem helper_1_6_step10 (a b c : Point) (habsurd : ¬ (|(a─b)| ≠ |(a─c)|)) :
    ¬ (|(a─b)| ≠ |(a─c)|) := by
  exact habsurd

end Elements.Book1
