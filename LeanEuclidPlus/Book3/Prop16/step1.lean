import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_step1
    (a : Point) (ABC : Circle) (AE : Line)
    (hsuppose1 : AE.intersectsCircle ABC)
    : ∃ c : Point, c.onLine AE ∧ c.onCircle ABC ∧ c ≠ a := by
  obtain ⟨p, q, hpC, hpL, hqC, hqL, hpq⟩ := intersections_circle_line ABC AE hsuppose1
  by_cases hp : p = a
  · exact ⟨q, hqL, hqC, fun hq => hpq (hp.trans hq.symm)⟩
  · exact ⟨p, hpL, hpC, hp⟩

end Elements.Book3
