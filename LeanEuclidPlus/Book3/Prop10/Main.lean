import SystemE

namespace Elements.Book3

-- orchestrator-agreed: matches enunciation — two distinct circles cannot share 3 distinct points ("cut at more than two points").
theorem proposition_10 : ∀ (ABC DEF : Circle),
  ABC ≠ DEF →
  ¬ ∃ (p q r : Point),
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    p.onCircle ABC ∧ q.onCircle ABC ∧ r.onCircle ABC ∧
    p.onCircle DEF ∧ q.onCircle DEF ∧ r.onCircle DEF :=
by
  sorry
