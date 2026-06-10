import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop47      -- a Book 1 result (lib `Book`)
--   import Book.Prop11
--   import Book2.Prop08     -- an earlier Book 2 result

namespace Elements.Book2

/-
═══════════════════════════════════════════════════════════════════════════════
STATEMENT — Prop 2.9
Convention: "square on X" = length-product |X|·|X|
            "double Y"     = 2 * Y
            (LeanEuclid, cf. Book 1 Prop 47/48; matches Book2/Prop01).
───────────────────────────────────────────────────────────────────────────────
If a straight-line is cut into equal and unequal (pieces, then) the (sum of the)
squares on the unequal pieces of the whole (straight-line) is double the (sum of
the) square on half (the straight-line) and (the square) on the (difference)
between the (equal and unequal) pieces.

  layout   : A ── C ── D ── B   (C halves AB; D cuts AB unequally, between C and B)
  premises : line AB (endpoints a b); c,d on AB;
             between a c b ∧ |a─c| = |c─b|   (cut equally at C)
             between c d b                   (cut unequally at D)
  GOAL     : square(AD) + square(DB) = 2 · (square(AC) + square(CD))
             |a─d|·|a─d| + |d─b|·|d─b| = 2 * (|a─c|·|a─c| + |c─d|·|c─d|)
═══════════════════════════════════════════════════════════════════════════════
-/

-- For let any straight-line $AB$ be cut---equally at $C$, and unequally at $D$.
-- I say that the (sum of the) squares on $AD$ and $DB$ is double the (sum of the
-- squares) on $AC$ and $CD$.
theorem proposition_9 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c b ∧ |(a─c)| = |(c─b)| ∧ between c d b →
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| =
    2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) :=
by
  euclid_intros
  -- NON-FAITHFUL proof (statement-correctness check only; a faithful proof follows
  -- Euclid via Prop 1.11 perpendicular CE, 1.3, 1.31 parallels, 1.5/1.6/1.29/1.32
  -- half-right-angles, and 1.47 Pythagoras — see data/texts_proofs/9.txt). The collinear
  -- order A─C─D─B reduces the goal to a ring identity once lengths are decomposed.
  have hac : |(a─c)| = |(c─d)| + |(d─b)| := by euclid_finish
  have had : |(a─d)| = |(a─c)| + |(c─d)| := by euclid_finish
  rw [had, hac]; ring

end Elements.Book2
