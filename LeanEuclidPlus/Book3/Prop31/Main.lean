import SystemE

namespace Elements.Book3

-- Clause (4) — "angle of the greater segment" / "angle of the lesser segment" (horn / curvilinear angle,
-- contained by arc and chord) — OMITTED: not expressible in System E (no curved-angle magnitude).
-- Clauses (1), (2), (3) — inscribed rectilinear angles — are stated below.
-- orchestrator-agreed (horn omitted): clauses 1-3 — angle in semicircle =∟, in greater segment <∟, in lesser >∟; semicircle
-- via between b e c (diameter), greater/lesser via b.opposingSides d AC. Clause-3 uses III.22 (cyclic
-- quad ABCD): full hyp is b.opposingSides d AC ∧ a.opposingSides c BD — added BD + distinctPointsOnLine b d BD
-- + a.opposingSides c BD (not derivable by SMT from on-circle alone). Horn clause 4 dropped per operator. FIXED.
theorem proposition_31 : ∀ (a b c d e : Point) (ABCD : Circle) (AC BD : Line),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
  e.isCentre ABCD ∧
  between b e c ∧
  distinctPointsOnLine a c AC ∧
  distinctPointsOnLine b d BD ∧
  b.opposingSides d AC ∧
  a.opposingSides c BD →
  ∠ b:a:c = ∟ ∧ ∠ a:b:c < ∟ ∧ ∠ a:d:c > ∟ :=
by
  sorry
