import SystemE

namespace Elements.Book3

-- orchestrator-agreed: cyclic quad, both opposite-angle pairs sum to ∟+∟; cyclic order via diagonal-crossing
-- (b.opposingSides d AC ∧ a.opposingSides c BD). Both pairs stated (Euclid proves one, "similarly" the other → both map).
theorem proposition_22 : ∀ (a b c d : Point) (ABCD : Circle) (AC BD : Line),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  b.opposingSides d AC ∧ a.opposingSides c BD →
  (∠ d:a:b + ∠ b:c:d = ∟ + ∟) ∧ (∠ a:b:c + ∠ c:d:a = ∟ + ∟) :=
by
  sorry
