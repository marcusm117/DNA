import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop47      -- a Book 1 result (lib `Book`)
--   import Book2.Prop04     -- an earlier Book 2 result

namespace Elements.Book2

/-
─────────────────────────────────────────────────────────────────────────────
STATEMENT (Prop 2.7)        faithful statement only.
Convention: "square on XY"            = |XY|·|XY|
            "rectangle contained X,Y" = |X|·|Y|   (length-product)
─────────────────────────────────────────────────────────────────────────────
"If a straight-line is cut at random, (then) the sum of the squares on the
 whole (straight-line), and one of the pieces (of the straight-line), is equal
 to twice the rectangle contained by the whole, and the said piece, and the
 square on the remaining piece."

Setup: straight-line AB cut at random at C (C between A and B).
       whole = AB ; said piece = BC ; remaining piece = CA.
GOAL : square(AB) + square(BC) = 2·rect(AB,BC) + square(CA)
       |AB|·|AB| + |BC|·|BC| = 2·(|AB|·|BC|) + |CA|·|CA|
-/

-- For let any straight-line $AB$ be cut, at random, at point $C$.
-- I say that the (sum of the) squares on $AB$ and $BC$ is equal to twice the
-- rectangle contained by $AB$ and $BC$, and the square on $CA$.
theorem proposition_7 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)| =
    2 * (|(a─b)| * |(b─c)|) + |(c─a)| * |(c─a)| :=
by
  euclid_intros
  -- NON-FAITHFUL proof (statement-correctness check only):
  -- between a c b gives |ab| = |ac| + |cb|, then the identity is algebra.
  have hsum : |(a─b)| = |(a─c)| + |(c─b)| := by euclid_finish
  have hca : |(c─a)| = |(a─c)| := by euclid_finish
  have hbc : |(b─c)| = |(c─b)| := by euclid_finish
  rw [hsum, hca, hbc]; ring

end Elements.Book2
