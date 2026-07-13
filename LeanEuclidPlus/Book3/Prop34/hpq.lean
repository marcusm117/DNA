import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_34_hpq (b : Point) (EF : Line) (hb_EF : b.onLine EF) :
    ∃ p q : Point, p.onLine EF ∧ q.onLine EF ∧ between p b q := by
  obtain ⟨p, hbp, hp_EF⟩ := exists_distincts_points_on_line EF b
  euclid_apply (extend_point EF p b) as q
  exact ⟨p, q, hp_EF, by euclid_finish, by euclid_finish⟩

end Elements.Book3
