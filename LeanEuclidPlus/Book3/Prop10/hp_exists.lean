import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_hp_exists
    (ABC : Circle) (AC NO : Line)
    (step4 : ∃ o : Point, o.isCentre ABC ∧ o.onLine AC)
    (step5 : ∃ o : Point, o.isCentre ABC ∧ o.onLine NO)
    : ∃ q : Point, q.onLine AC ∧ q.onLine NO := by
  obtain ⟨o1, ho1, ho1AC⟩ := step4
  obtain ⟨o2, ho2, ho2NO⟩ := step5
  have heq : o1 = o2 := by
    have := centre_unique o1 o2 ABC ⟨ho1, ho2⟩
    exact this
  exact ⟨o1, ho1AC, heq ▸ ho2NO⟩

end Elements.Book3
