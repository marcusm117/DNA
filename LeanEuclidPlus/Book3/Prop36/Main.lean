import SystemE

namespace Elements.Book3

-- orchestrator-agreed: external point, secant·external = tangent² — |da|·|dc|=|db|²; secant via between d c a, tangent via
-- touches (inline). Single statement covers both proof cases (secant through/not-through center). Clean.
theorem proposition_36 : ∀ (a b c d : Point) (ABC : Circle) (DB : Line),
    a.onCircle ABC ∧ c.onCircle ABC ∧ d.outsideCircle ABC ∧
    between d c a ∧
    d.onLine DB ∧ b.onLine DB ∧ b.onCircle ABC ∧ ¬ DB.intersectsCircle ABC →
    |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)| :=
by
  sorry
