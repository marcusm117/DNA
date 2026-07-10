import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step28
    (ABCD : Circle) (f g h : Point)
    (step27 : ¬ (∃ k : Point, k.onCircle ABCD ∧ |(f─k)| = |(f─g)| ∧ k ≠ g ∧ k ≠ h))
    : ∀ n : Point, n.onCircle ABCD → |(f─n)| = |(f─g)| → n = g ∨ n = h := by
  intro n hn_on hn_eq
  by_contra h_case
  have hng : n ≠ g := fun heq => h_case (Or.inl heq)
  have hnh : n ≠ h := fun heq => h_case (Or.inr heq)
  exact step27 ⟨n, hn_on, hn_eq, hng, hnh⟩

end Elements.Book3
