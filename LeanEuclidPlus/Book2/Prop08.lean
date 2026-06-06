import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop47      -- a Book 1 result (lib `Book`)
--   import Book2.Prop04     -- an earlier Book 2 result

namespace Elements.Book2

/-
Convention (cf. Prop 2.1 / Book 1 Prop 47, axiom `rectangle_area`):
  "rectangle contained by X and Y"  = |X| * |Y|   (area of the figure)
  "square on X"                      = |X| * |X|
  "AB cut at random at C"            = C strictly between A and B.
  "square described on AB and BC, as on one (complete straight-line)"
        = the square on a single segment of length AB + BC
        = (|AB| + |BC|) * (|AB| + |BC|).
   (In the proof Euclid produces D past B with BD = BC, so AD = AB + BC,
    and erects the square AEFD on AD.)
Diagram order: A — C — B.
-/

-- If a straight-line is cut at random, (then) four times the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), plus the square on the remaining piece, is equal to the square described on the whole and the former piece, as on one (complete straight-line). For let any straight-line $AB$ be cut, at random, at point $C$. I say that four times the rectangle contained by $AB$ and $BC$, plus the square on $AC$, is equal to the square described on $AB$ and $BC$, as on one (complete straight-line).
theorem proposition_8 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ between a c b →
  4 * (|(a─b)| * |(b─c)|) + |(a─c)| * |(a─c)| =
    (|(a─b)| + |(b─c)|) * (|(a─b)| + |(b─c)|) :=
by
  -- NON-FAITHFUL proof: only here to sanity-check the statement is correct.
  -- AB = AC+CB, BC = CB; with x=AC, y=CB: 4(x+y)y + x² = (x+2y)². ring.
  euclid_intros
  have hab : |(a─b)| = |(a─c)| + |(c─b)| := by euclid_finish
  have hbc : |(b─c)| = |(c─b)| := by euclid_finish
  rw [hab, hbc]; ring

end Elements.Book2
