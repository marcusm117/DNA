import SystemE

namespace Elements.Book3

-- orchestrator-agreed: converse of 3.36 — |ad|·|dc|=|db|² ⟹ DB touches the circle (goal = touches inline, self-contained). Clean.
theorem proposition_37 : ∀ (d a c b : Point) (ABC : Circle) (DB : Line),
  d.outsideCircle ABC ∧
  a.onCircle ABC ∧ c.onCircle ABC ∧ between d c a ∧
  b.onCircle ABC ∧ d.onLine DB ∧ b.onLine DB ∧
  |(a─d)| * |(d─c)| = |(d─b)| * |(d─b)| →
  (∃ p : Point, p.onLine DB ∧ p.onCircle ABC) ∧ ¬ DB.intersectsCircle ABC :=
by
  sorry
