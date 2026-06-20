import SystemE.Theory.Relations

-- a trailing comment that must NOT leak into the prior decl's signature
/-- If `b` is between `a` and `c` then symmetry holds. -/
axiom between_symm : ∀ (a b c : Point), between a b c →
  (between c b a) ∧ (a ≠ b) ∧ (a ≠ c) ∧ ¬(between b a c)

axiom inside_not_on_circle : ∀ (a : Point) (α : Circle),
  a.insideCircle α → ¬(a.onCircle α)
