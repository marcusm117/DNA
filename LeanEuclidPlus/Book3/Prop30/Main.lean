import SystemE

namespace Elements.Book3

-- orchestrator-agreed: construction — bisect a given arc → ∃ d on the circle with equal sub-arcs (∠a:o:d=∠d:o:b). Arc
-- equality as goal keeps Euclid's "circumference AD=DB" a real claim. Center o given (needed to state arc). Proof-faithful.
theorem proposition_30 : ∀ (a b o : Point) (ADB : Circle),
  a.onCircle ADB ∧ b.onCircle ADB ∧ a ≠ b ∧ o.isCentre ADB →
  ∃ d : Point, d.onCircle ADB ∧ ∠ a:o:d = ∠ d:o:b :=
by
  sorry
