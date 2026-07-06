import SystemE

namespace Elements.Book3

-- proof-faithfulness: "same segment BAED"→a.sameSide e BD (primer convention). Euclid's proof finds center F then
-- applies [3.20] TWICE (∠BFD=2·∠BAD, ∠BFD=2·∠BED). Prop 3.20's signature requires c.sameSide e AB (vertex on
-- center's side). Current segment BAED is the MAJOR arc; a.sameSide e BD alone does not fix which side the center
-- is on, so both [3.20] applications would be unsupported. Fix: add center f with f.isCentre ABCD ∧ a.sameSide f BD.
-- Then e.sameSide f BD follows by transitivity (a.sameSide e BD ∧ a.sameSide f BD), enabling both [3.20] steps.
theorem proposition_21 : ∀ (a b d e f : Point) (BD : Line) (ABCD : Circle),
  f.isCentre ABCD ∧
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ d.onCircle ABCD ∧ e.onCircle ABCD ∧
  distinctPointsOnLine b d BD ∧
  a.sameSide e BD ∧
  a.sameSide f BD →
  ∠ b:a:d = ∠ b:e:d :=
by
  sorry
