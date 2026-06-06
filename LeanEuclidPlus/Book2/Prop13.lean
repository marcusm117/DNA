import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop47      -- a Book 1 result (lib `Book`)
--   import Book2.Prop04     -- an earlier Book 2 result

namespace Elements.Book2

/-
─────────────────────────────────────────────────────────────────────────────
STATEMENT (Prop 2.13)        faithful statement only (proof deferred: sorry).
Convention: "square on XY"            = |XY|·|XY|
            "rectangle contained X,Y" = |X|·|Y|   (length-product)
─────────────────────────────────────────────────────────────────────────────
"In acute-angled triangles, the square on the side subtending the acute angle
 is less than the (sum of the) squares on the sides containing the acute angle
 by twice the (rectangle) contained by one of the sides around the acute angle,
 to which a perpendicular (straight-line) falls, and the (straight-line) cut
 off inside (the triangle) by the perpendicular (straight-line) towards the
 acute angle."

Setup: ABC an acute-angled triangle, the angle at B acute.
       AD drawn from A perpendicular to BC, foot D inside (between b and c).
       side subtending the acute angle B = AC.
       sides containing B = CB and BA.
       side to which the perpendicular falls = CB.
       cut off inside towards the acute angle = BD.
GOAL : square(AC) is less than square(CB)+square(BA) by 2·rect(CB,BD), i.e.
       |AC|·|AC| + 2·(|CB|·|BD|) = |CB|·|CB| + |BA|·|BA|
-/

-- Let $ABC$ be an acute-angled triangle, having the angle at (point) $B$ acute.
-- And let $AD$ be drawn from point $A$, perpendicular to $BC$ [Prop.~1.12].
-- I say that the square on $AC$ is less than the (sum of the) squares on $CB$
-- and $BA$ by twice the rectangle contained by $CB$ and $BD$.
theorem proposition_13 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧
  (∠ a:b:c : ℝ) < ∟ ∧ (∠ b:c:a : ℝ) < ∟ ∧ (∠ c:a:b : ℝ) < ∟ ∧
  d.onLine BC ∧ between b d c ∧ (∠ a:d:c : ℝ) = ∟ →
  |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|) =
    |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| :=
by
  euclid_intros
  sorry

end Elements.Book2
