import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop47      -- a Book 1 result (lib `Book`)
--   import Book2.Prop04     -- an earlier Book 2 result

namespace Elements.Book2

/-
─────────────────────────────────────────────────────────────────────────────
STATEMENT (Prop 2.4)        faithful statement only.
Convention: "square on XY"            = |XY|·|XY|
            "rectangle contained X,Y" = |X|·|Y|   (length-product)
─────────────────────────────────────────────────────────────────────────────
"If a straight-line is cut at random, (then) the square on the whole
 (straight-line) is equal to the (sum of the) squares on the pieces (of the
 straight-line), and twice the rectangle contained by the pieces."

Setup: straight-line AB cut at random at C (C between A and B).
GOAL : square(AB) = square(AC) + square(CB) + 2·rect(AC,CB)
       |AB|·|AB| = |AC|·|AC| + |CB|·|CB| + 2·(|AC|·|CB|)
-/

-- For let the straight-line $AB$ be cut, at random, at (point) $C$.
-- I say that the square on $AB$ is equal to the (sum of the) squares on $AC$
-- and $CB$, and twice the rectangle contained by $AC$ and $CB$.
theorem proposition_4 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(a─b)| =
    |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) :=
by
  euclid_intros
  -- NON-FAITHFUL proof (statement-correctness check only):
  -- between a c b gives |ab| = |ac| + |cb|, then the identity is algebra.
  have hsum : |(a─b)| = |(a─c)| + |(c─b)| := by euclid_finish
  rw [hsum]; ring

end Elements.Book2