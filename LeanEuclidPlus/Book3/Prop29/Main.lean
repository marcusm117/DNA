import SystemE

namespace Elements.Book3

-- orchestrator-agreed: converse of 3.28 — equal circles + equal arcs (∠b:k:c=∠e:l:f) ⟹ equal chords (|bc|=|ef|).
-- NON-circular (arc in hyp, chord in goal; proof via SAS [1.4]). Proof-faithful.
theorem proposition_29 : ∀ (b c e f k l : Point) (ABC DEF : Circle),
  k.isCentre ABC ∧ l.isCentre DEF ∧
  b.onCircle ABC ∧ c.onCircle ABC ∧
  e.onCircle DEF ∧ f.onCircle DEF ∧
  |(k─b)| = |(l─e)| ∧
  ∠ b:k:c = ∠ e:l:f →
  |(b─c)| = |(e─f)| :=
by
  sorry
