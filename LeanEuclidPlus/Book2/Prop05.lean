import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop47      -- a Book 1 result (lib `Book`)
--   import Book2.Prop04     -- an earlier Book 2 result

namespace Elements.Book2

/-
Convention (cf. Prop 2.1 / Book 1 Prop 47, axiom `rectangle_area`):
  "rectangle contained by X and Y"  = |X| * |Y|   (area of the figure)
  "square on X"                      = |X| * |X|
  "AB cut equally at C"   = C bisects AB:  |AC| = |CB|.
  "AB cut unequally at D" = D ≠ C; with the A–C–D–B ordering below this is
                            automatic (AD = AC+CD > CB > CB−CD = DB).
Diagram order: A — C — D — B  (C midpoint, D between C and B).
-/

-- If a straight-line is cut into equal and unequal (pieces, then) the rectangle contained by the unequal pieces of the whole (straight-line), plus the square on the (difference) between the (equal and unequal) pieces, is equal to the square on half (of the straight-line). For let any straight-line $AB$ be cut---equally at $C$, and unequally at $D$. I say that the rectangle contained by $AD$ and $DB$, plus the square on $CD$, is equal to the square on $CB$.
theorem proposition_5 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c d ∧ between c d b ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)| = |(c─b)| * |(c─b)| :=
by
  -- NON-FAITHFUL proof: only here to sanity-check the statement is correct.
  -- AD = AC+CD = CB+CD,  DB = CB−CD  ⇒  AD·DB = CB²−CD², then +CD² = CB².
  euclid_intros
  have had : |(a─d)| = |(c─b)| + |(c─d)| := by euclid_finish
  have hdb : |(c─d)| + |(d─b)| = |(c─b)| := by euclid_finish
  have hdb' : |(d─b)| = |(c─b)| - |(c─d)| := by rw [← hdb]; ring
  rw [had, hdb']; ring

end Elements.Book2
