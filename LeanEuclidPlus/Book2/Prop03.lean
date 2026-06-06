import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop46      -- a Book 1 result (lib `Book`)
--   import Book.Prop31
--   import Book2.Prop01     -- an earlier Book 2 result

namespace Elements.Book2

/-
═══════════════════════════════════════════════════════════════════════════════
STATEMENT — Prop 2.3
Convention: "rectangle contained by X and Y" = length-product |X|·|Y|
            "square on X"                     = |X|·|X|
            (LeanEuclid, cf. Book 1 Prop 47/48; matches Book2/Prop01).
───────────────────────────────────────────────────────────────────────────────
If a straight-line is cut at random, (then) the rectangle contained by the whole
(straight-line), and one of the pieces (of the straight-line), is equal to the
rectangle contained by (both of) the pieces, and the square on the aforementioned
piece.

  premises : line AB (endpoints a b); point c cutting AB at random  (between a c b)
  GOAL     : rect(AB,BC) = rect(AC,CB) + square(BC)
             |a─b|·|b─c| = |a─c|·|c─b| + |b─c|·|b─c|
═══════════════════════════════════════════════════════════════════════════════
-/

-- For let the straight-line $AB$ be cut, at random, at (point) $C$. I say that the
-- rectangle contained by $AB$ and $BC$ is equal to the rectangle contained by
-- $AC$ and $CB$, plus the square on $BC$.
theorem proposition_3 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| :=
by
  euclid_intros
  -- NON-FAITHFUL proof (statement-correctness check only; a faithful proof follows
  -- Euclid via Prop 1.46 square on CB + Prop 1.31 parallel through A — see texts_proofs/3.txt).
  -- Betweenness ⇒ |a─b| = |a─c| + |c─b|, and |c─b| = |b─c|, so the goal is a ring identity.
  have hsum : |(a─b)| = |(a─c)| + |(c─b)| := by euclid_finish
  have hsym : |(c─b)| = |(b─c)| := by euclid_finish
  rw [hsum, hsym]; ring

end Elements.Book2