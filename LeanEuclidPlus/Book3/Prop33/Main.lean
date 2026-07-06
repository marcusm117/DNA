import SystemE

namespace Elements.Book3

-- orchestrator-agreed: construction — on given line AB + given angle C, ∃ circle thru A,B with a vertex e where inscribed
-- ∠a:e:b = C. "segment admitting angle"→∃ circle+inscribed angle. Side condition on e omitted (∃ covers all cases) — noted.
theorem proposition_33 : ∀ (a b c₁ c c₂ : Point),
  a ≠ b →
  ∃ (α : Circle) (e : Point), a.onCircle α ∧ b.onCircle α ∧ e.onCircle α ∧ ∠ a:e:b = ∠ c₁:c:c₂ :=
by
  sorry
