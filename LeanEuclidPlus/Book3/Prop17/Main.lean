import SystemE

namespace Elements.Book3

-- orchestrator-agreed: construction — from external point, ∃ line through it that touches the circle. Matches enunciation.
theorem proposition_17 : ∀ (a : Point) (BCD : Circle),
  a.outsideCircle BCD →
  ∃ L : Line, a.onLine L ∧ (∃ p : Point, p.onLine L ∧ p.onCircle BCD) ∧ ¬ L.intersectsCircle BCD :=
by
  sorry
