import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop47      -- a Book 1 result (lib `Book`)
--   import Book2.Prop04     -- an earlier Book 2 result

namespace Elements.Book2

/-
Convention (cf. Prop 2.1 / LeanEuclid):
  "rectangle contained by X and Y"  = |X| * |Y|
  "square on X"                      = |X| * |X|   (cf. Book 1 Prop 47)
"AB cut at random at C" = C lies strictly between A and B on line AB.
-/

-- If a straight-line is cut at random, (then) the (sum of the) rectangle(s) contained by the whole (straight-line), and each of the pieces (of the straight-line), is equal to the square on the whole. For let the straight-line $AB$ be cut, at random, at point $C$. I say that the rectangle contained by $AB$ and $BC$, plus the rectangle contained by $BA$ and $AC$, is equal to the square on $AB$.
theorem proposition_2 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ between a c b →
  |(a─b)| * |(b─c)| + |(b─a)| * |(a─c)| = |(a─b)| * |(a─b)| :=
by
  -- NON-FAITHFUL proof: only here to sanity-check the statement is correct.
  -- (between a c b ⇒ |a─c|+|c─b| = |a─b|; segment symmetry; then ring.)
  euclid_intros
  have hsum : |(a─c)| + |(c─b)| = |(a─b)| := by euclid_finish
  have hbc : |(b─c)| = |(c─b)| := by euclid_finish
  have hba : |(b─a)| = |(a─b)| := by euclid_finish
  rw [hbc, hba]
  have : |(a─b)| = |(a─c)| + |(c─b)| := hsum.symm
  rw [this]; ring

end Elements.Book2