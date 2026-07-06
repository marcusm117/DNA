import SystemE

namespace Elements.Book3

-- orchestrator-agreed: equal circles + equal chords (|ab|=|de|) ⟹ equal arcs (∠a:k:b=∠d:l:e). NON-circular (chord in hyp,
-- arc in goal; proof via SSS [1.8]). Minor-arc only in goal (major-arc sentence derived in proof). Proof-faithful.
theorem proposition_28 : ∀ (a b d e k l : Point) (ABC DEF : Circle),
  a.onCircle ABC ∧ b.onCircle ABC ∧
  d.onCircle DEF ∧ e.onCircle DEF ∧
  k.isCentre ABC ∧ l.isCentre DEF ∧
  |(k─a)| = |(l─d)| ∧
  a ≠ b ∧ d ≠ e ∧
  |(a─b)| = |(d─e)| →
  ∠ a:k:b = ∠ d:l:e :=
by
  sorry
