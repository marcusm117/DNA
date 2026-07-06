import SystemE

namespace Elements.Book3

-- orchestrator-agreed: intersecting chords — rectangle=length-product; two chords crossing at E ⟹ |ae|·|ec|=|be|·|ed|. Clean.
theorem proposition_35 : ∀ (a b c d e : Point) (ABCD : Circle),
    a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
    between a e c ∧ between b e d →
    |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)| :=
by
  sorry
