import SystemE

namespace Elements.Book3

-- orchestrator-agreed: diameter greatest (|ad|>|bc|) + nearer-to-center-greater (|eh|<|ek| → |bc|>|fg|), via Euclid's named
-- chords BC,FG and perpendicular-foot distance (Def 3.5). Same specific-instances style as III.7/8. Faithful.
theorem proposition_15 : ∀ (a b c d e f g h k : Point) (ABCD : Circle) (BC FG : Line),
  e.isCentre ABCD ∧
  a.onCircle ABCD ∧ d.onCircle ABCD ∧ between a e d ∧
  b.onCircle ABCD ∧ c.onCircle ABCD ∧ distinctPointsOnLine b c BC ∧
  f.onCircle ABCD ∧ g.onCircle ABCD ∧ distinctPointsOnLine f g FG ∧
  h.onLine BC ∧ ∠ e:h:b = ∟ ∧
  k.onLine FG ∧ ∠ e:k:f = ∟ ∧
  |(e─h)| < |(e─k)| →
  |(a─d)| > |(b─c)| ∧ |(b─c)| > |(f─g)| :=
by
  sorry
