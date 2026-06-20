import SystemE.Theory.Relations

axiom line_from_points : ∀ (a b : Point), a ≠ b → ∃ L : Line, (a.onLine L) ∧ (b.onLine L)

axiom intersection_lines : ∀ (L M : Line), L.intersectsLine M → ∃ a : Point, (a.onLine L) ∧ (a.onLine M)
