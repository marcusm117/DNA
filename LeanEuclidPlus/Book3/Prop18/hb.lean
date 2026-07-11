import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_18_hb (ABC : Circle) (c : Point) :
    ∃ b : Point, b.onCircle ABC ∧ b ≠ c := by
  obtain ⟨b, hne, honc⟩ := exists_distinct_point_on_circle ABC c
  exact ⟨b, honc, hne⟩

end Elements.Book3
