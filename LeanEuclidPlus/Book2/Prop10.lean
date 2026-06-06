import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop47      -- a Book 1 result (lib `Book`)
--   import Book2.Prop04     -- an earlier Book 2 result

namespace Elements.Book2

/-
─────────────────────────────────────────────────────────────────────────────
STATEMENT (Prop 2.10)        faithful statement only.
Convention: "square on XY"            = |XY|·|XY|
─────────────────────────────────────────────────────────────────────────────
"If a straight-line is cut in half, and any straight-line added to it
 straight-on, (then) the sum of the square on the whole (straight-line) with
 the (straight-line) having been added, and the (square) on the (straight-line)
 having been added, is double the (sum of the square) on half (the
 straight-line), and the square described on the sum of half (the
 straight-line) and (straight-line) having been added, as on one (complete
 straight-line)."

Setup: straight-line AB cut in half at C  (C midpoint: |AC| = |CB|),
       straight-line BD added straight-on  (order A–C–B–D along the line).
       whole-with-added = AD ; added = DB ; half = AC ;
       half+added = CD.
GOAL : square(AD) + square(DB) = 2·(square(AC) + square(CD))
       |AD|·|AD| + |DB|·|DB| = 2·(|AC|·|AC| + |CD|·|CD|)
-/

-- For let any straight-line $AB$ be cut in half at (point) $C$, and let any
-- straight-line $BD$ be added to it straight-on.
-- I say that the (sum of the) squares on $AD$ and $DB$ is double the (sum of
-- the) squares on $AC$ and $CD$.
theorem proposition_10 : ∀ (a b c d : Point) (AD : Line),
  distinctPointsOnLine a d AD ∧ c.onLine AD ∧ b.onLine AD ∧
  between a c b ∧ between a b d ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| =
    2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) :=
by
  euclid_intros
  -- NON-FAITHFUL proof (statement-correctness check only):
  -- segment additions along A–C–B–D, then the identity is algebra.
  have h1 : |(a─d)| = |(a─c)| + |(c─d)| := by euclid_finish
  have h2 : |(c─d)| = |(c─b)| + |(b─d)| := by euclid_finish
  have h3 : |(a─c)| = |(c─b)| := by euclid_finish
  have h4 : |(d─b)| = |(b─d)| := by euclid_finish
  rw [h1, h2, h4, h3]; ring

end Elements.Book2
