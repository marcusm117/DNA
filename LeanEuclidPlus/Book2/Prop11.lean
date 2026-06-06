import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop47      -- a Book 1 result (lib `Book`)
--   import Book2.Prop04     -- an earlier Book 2 result

namespace Elements.Book2

/-
Convention (cf. Prop 2.1 / Book 1 Prop 47, axiom `rectangle_area`):
  "rectangle contained by X and Y"  = |X| * |Y|   (area of the figure)
  "square on X"                      = |X| * |X|
This is a CONSTRUCTION proposition ("To cut a given straight-line such
that …"), so it is stated existentially, like Book 1's Prop 1/10:
  given AB, produce a cut point H on AB with the required area equality.
Diagram order: A — H — B.
-/

-- To cut a given straight-line such that the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the square on the remaining piece. Let $AB$ be the given straight-line. So it is required to cut $AB$ such that the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the square on the remaining piece. [I say that $AB$ has been cut at $H$ such as to make the rectangle contained by $AB$ and $BH$ equal to the square on $AH$.]
theorem proposition_11 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ h : Point, between a h b ∧
    |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| :=
by
  -- PROOF DEFERRED (statement phase). This is a CONSTRUCTION goal (∃ h): unlike
  -- the equational props (2.2/2.5/2.8) there is no `ring` shortcut — the cut
  -- point must actually be exhibited, and since the golden section is irrational
  -- a √5 length has to be built (perpendicular at A + Pythagoras, Euclid's
  -- square ABDC [1.46], bisect AC [1.10], EF=EB [1.3]). Left as `sorry` for now.
  --
  -- Statement is correct/satisfiable: with |AB| = s, |AH| = x (so |BH| = s − x),
  -- s·(s−x) = x²  ⇔  x = s·(√5 − 1)/2 ≈ 0.618 s ∈ (0, s) — the golden section.
  sorry

end Elements.Book2
