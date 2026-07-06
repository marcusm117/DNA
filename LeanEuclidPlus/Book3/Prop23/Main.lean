import SystemE

namespace Elements.Book3

-- Proof-faithful: Euclid constructs line ACD through both segments (sentence: "let ACD be drawn through
-- the segments"), placing c between a and d (`between a c d`).  That collinearity is the SOLE reason
-- ∠ACB is the exterior angle of triangle BCD, which I.16 then compares to the interior ∠ADB.
-- Without `between a c d` the I.16 sentence ("the external to the internal") has no home.
-- Sentence map:
--   S1  setup: circles ACB, ADB through chord ab; c on ACB, d on ADB, same side, ACB ≠ ADB
--   S2  construction: "let ACD be drawn" → between a c d; "CB and DB joined" (no extra hyp needed)
--   S3  "angle ACB equal to ADB" [Def. 3.11] → step from ∠a:c:b = ∠a:d:b hypothesis
--   S4  "external to the internal, impossible" [I.16] → exterior-angle at c (from between a c d)
--       gives ∠a:c:b > ∠a:d:b; contradicts S3 → False
theorem proposition_23 : ∀ (a b c d : Point) (AB : Line) (ACB ADB : Circle),
  distinctPointsOnLine a b AB ∧
  a.onCircle ACB ∧ b.onCircle ACB ∧ c.onCircle ACB ∧
  a.onCircle ADB ∧ b.onCircle ADB ∧ d.onCircle ADB ∧
  c.sameSide d AB ∧
  between a c d ∧
  ∠ a:c:b = ∠ a:d:b ∧
  ACB ≠ ADB →
  False :=
by
  sorry
