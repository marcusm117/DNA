import SystemE

namespace Elements.Book3

-- orchestrator-agreed: tangent-chord angle = inscribed angle in the ALTERNATE segment, BOTH sides (conjunction). touches
-- (inline) + alternate=opposingSides; SPECIFIC vertices a,c (proof-faithful, not ∀). Config-dependent (BD not diameter) — noted.
theorem proposition_32 : ∀ (b a d c e f : Point) (ABCD : Circle) (EF BD : Line),
  b.onLine EF ∧ b.onCircle ABCD ∧ ¬ EF.intersectsCircle ABCD ∧
  e.onLine EF ∧ f.onLine EF ∧ between e b f ∧
  b.onLine BD ∧ d.onCircle ABCD ∧ d.onLine BD ∧ b ≠ d ∧
  a.onCircle ABCD ∧ c.onCircle ABCD ∧
  a.opposingSides f BD ∧ c.opposingSides e BD →
  ∠ f:b:d = ∠ b:a:d ∧ ∠ e:b:d = ∠ d:c:b :=
by
  sorry
