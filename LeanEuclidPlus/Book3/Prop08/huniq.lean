import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_8_huniq
    (ABC : Circle) (k d b0 : Point)
    (step32 : ¬∃ n : Point, n.onCircle ABC ∧ |(d─n)| = |(d─k)| ∧ n ≠ k ∧ n ≠ b0) :
    ∀ n : Point, n.onCircle ABC → |(d─n)| = |(d─k)| → n = k ∨ n = b0 := by
  intro n hn_circ hn_dist
  by_contra h
  apply step32
  exact ⟨n, hn_circ, hn_dist, fun hk => h (Or.inl hk), fun hb => h (Or.inr hb)⟩

end Elements.Book3
