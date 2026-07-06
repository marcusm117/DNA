import SystemE

namespace Elements.Book3

-- orchestrator-agreed: touching distinct circles ⟹ contact point is unique (∀ two common points coincide). Covers both cases.
theorem proposition_13 : ∀ (ABDC EBFD : Circle),
  ABDC ≠ EBFD ∧ (∃ p : Point, p.onCircle ABDC ∧ p.onCircle EBFD) ∧ ¬ ABDC.intersectsCircle EBFD →
  ∀ (p q : Point), p.onCircle ABDC ∧ p.onCircle EBFD ∧ q.onCircle ABDC ∧ q.onCircle EBFD → p = q :=
by
  sorry
