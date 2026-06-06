import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop46      -- a Book 1 result (lib `Book`)
--   import Book.Prop31
--   import Book2.Prop05     -- an earlier Book 2 result

namespace Elements.Book2

/-
═══════════════════════════════════════════════════════════════════════════════
STATEMENT — Prop 2.6
Convention: "rectangle contained by X and Y" = length-product |X|·|Y|
            "square on X"                     = |X|·|X|
            (LeanEuclid, cf. Book 1 Prop 47/48; matches Book2/Prop01).
───────────────────────────────────────────────────────────────────────────────
If a straight-line is cut in half, and any straight-line added to it straight-on,
(then) the rectangle contained by the whole (straight-line) with the
(straight-line) having been added, and the (straight-line) having been added, plus
the square on half (of the original straight-line), is equal to the square on the
sum of half (of the original straight-line) and the (straight-line) having been
added.

  layout   : A ── C ── B ── D   (C halves AB; BD added straight-on beyond B)
  premises : line AB (endpoints a b); c,d on AB;
             between a c b ∧ |a─c| = |c─b|   (AB cut in half at C)
             between a b d                   (BD added straight-on beyond B)
  GOAL     : rect(AD,DB) + square(CB) = square(CD)
             |a─d|·|d─b| + |c─b|·|c─b| = |c─d|·|c─d|
═══════════════════════════════════════════════════════════════════════════════
-/

-- For let any straight-line $AB$ be cut in half at point $C$, and let any
-- straight-line $BD$ be added to it straight-on. I say that the rectangle
-- contained by $AD$ and $DB$, plus the square on $CB$, is equal to the square on $CD$.
theorem proposition_6 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c b ∧ |(a─c)| = |(c─b)| ∧ between a b d →
  |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| :=
by
  euclid_intros
  -- NON-FAITHFUL proof (statement-correctness check only; a faithful proof follows
  -- Euclid via Prop 1.46 square CEFD on CD, Prop 1.31 parallels, 1.36/1.43 gnomon —
  -- see texts_proofs/6.txt). The collinear order A─C─B─D reduces the goal to a ring
  -- identity once segment lengths are decomposed.
  have h1 : |(a─d)| = |(a─c)| + |(c─b)| + |(b─d)| := by euclid_finish
  have h2 : |(c─d)| = |(c─b)| + |(b─d)| := by euclid_finish
  have h3 : |(d─b)| = |(b─d)| := by euclid_finish
  rw [h1, h2, h3]
  have hcb : |(a─c)| = |(c─b)| := by euclid_finish
  rw [hcb]; ring

end Elements.Book2
