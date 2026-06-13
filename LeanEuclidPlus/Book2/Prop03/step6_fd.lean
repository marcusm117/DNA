import SystemE

namespace Elements.Book2

/- sub-fact: f ≠ d. between e d f makes d strictly between e and f, so f ≠ d. -/
set_option systemE.solverTime 30 in
theorem helper_2_step6_fd (d e f : Point) (hedf : between e d f) : f ≠ d := by
  euclid_finish

end Elements.Book2
