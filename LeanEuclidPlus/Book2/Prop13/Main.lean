import SystemE
import Book1.Prop12.Main
import Book2.Prop13.step1
import Book2.Prop13.step2
import Book2.Prop13.step3
import Book2.Prop13.step4
import Book2.Prop13.step5
import Book2.Prop13.step6
import Book2.Prop13.step7
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem proposition_13 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧
  (∠ a:b:c : ℝ) < ∟ ∧ (∠ b:c:a : ℝ) < ∟ ∧ (∠ c:a:b : ℝ) < ∟ ∧
  d.onLine BC ∧ between b d c ∧ (∠ a:d:c : ℝ) = ∟ →
  |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|) =
    |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| := by
  euclid_intros
  -- [Prop.~1.12] construction: a perpendicular from A to BC. `d` is already a hypothesis
  -- (the foot, with its right angle), so this produces only a witness `d0` recording the citation.
  euclid_apply (Elements.Book1.proposition_12 b c a BC) as d0
  euclid_intro_sentence "2.13.0"
    "In acute-angled triangles, the square on the side subtending the acute angle is less than the (sum of the) squares on the sides containing the acute angle by twice the (rectangle) contained by one of the sides around the acute angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off inside (the triangle) by the perpendicular (straight-line) towards the acute angle. Let $ABC$ be an acute-angled triangle, having the angle at (point) $B$ acute. And let $AD$ be drawn from point $A$, perpendicular to $BC$ [Prop.~1.12]. I say that the square on $AC$ is less than the (sum of the) squares on $CB$ and $BA$ by twice the rectangle contained by $CB$ and $BD$."

  -- @assumption_valid
  have step1_assumption1 : between b d c := by assumption
  -- @assumption ("the straight-line $CB$ has been cut, at random, at (point) $D$", between b d c)
  euclid_sentence "2.13.1"
    "For since the straight-line $CB$ has been cut, at random, at (point) $D$, the (sum of the) squares on $CB$ and $BD$ is thus equal to twice the rectangle contained by $CB$ and $BD$, and the square on $DC$ [Prop.~2.7]."
    (step1 : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| = 2 * (|(c─b)| * |(b─d)|) + |(d─c)| * |(d─c)|) := by euclid_apply (helper_2_13_step1 c b d BC (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "the straight-line $CB$ has been cut, at random, at (point) $D$" (show between b d c; assumption)))

  euclid_sentence "2.13.2"
    "Let the square on $DA$ be added to both."
    (step2 : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| = 2 * (|(c─b)| * |(b─d)|) + |(d─c)| * |(d─c)| + |(d─a)| * |(d─a)|) := by euclid_apply (helper_2_13_step2 c b d a (by euclid_assumption "" (show |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| = 2 * (|(c─b)| * |(b─d)|) + |(d─c)| * |(d─c)|; assumption)))

  euclid_sentence "2.13.3"
    "Thus, the (sum of the) squares on $CB$, $BD$, and $DA$ is equal to twice the rectangle contained by $CB$ and $BD$, and the (sum of the) squares on $AD$ and $DC$."
    (step3 : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| = 2 * (|(c─b)| * |(b─d)|) + |(a─d)| * |(a─d)| + |(d─c)| * |(d─c)|) := by euclid_apply (helper_2_13_step3 c b d a (by euclid_assumption "" (show |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| = 2 * (|(c─b)| * |(b─d)|) + |(d─c)| * |(d─c)| + |(d─a)| * |(d─a)|; assumption)))

  -- @assumption_valid
  have step4_assumption1 : ∠ a:d:c = ∟ := by assumption
  -- @assumption ("the angle at (point) $D$ is a right-angle", ∠ a:d:c = ∟)
  euclid_sentence "2.13.4"
    "But, the (square) on $AB$ (is) equal to the (sum of the squares) on $BD$ and $DA$. For the angle at (point) $D$ is a right-angle [Prop.~1.47]."
    (step4 : |(a─b)| * |(a─b)| = |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)|) := by euclid_apply (helper_2_13_step4 a b c d AB BC CA (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CA; assumption)) (by euclid_assumption "" (show a.onLine CA; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ CA; assumption)) (by euclid_assumption "" (show CA ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show between b d c; assumption)) (by euclid_assumption "the angle at (point) $D$ is a right-angle" (show ∠ a:d:c = ∟; assumption)))

  euclid_sentence "2.13.5"
    "And the (square) on $AC$ (is) equal to the (sum of the squares) on $AD$ and $DC$ [Prop.~1.47]."
    (step5 : |(a─c)| * |(a─c)| = |(a─d)| * |(a─d)| + |(d─c)| * |(d─c)|) := by euclid_apply (helper_2_13_step5 a b c d AB BC CA (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CA; assumption)) (by euclid_assumption "" (show a.onLine CA; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ CA; assumption)) (by euclid_assumption "" (show CA ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show between b d c; assumption)) (by euclid_assumption "" (show ∠ a:d:c = ∟; assumption)))

  euclid_sentence "2.13.6"
    "Thus, the (sum of the squares) on $CB$ and $BA$ is equal to the (square) on $AC$, and twice the (rectangle contained) by $CB$ and $BD$."
    (step6 : |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| = |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|)) := by euclid_apply (helper_2_13_step6 a b c d (by euclid_assumption "" (show |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| = 2 * (|(c─b)| * |(b─d)|) + |(a─d)| * |(a─d)| + |(d─c)| * |(d─c)|; assumption)) (by euclid_assumption "" (show |(a─b)| * |(a─b)| = |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)|; assumption)) (by euclid_assumption "" (show |(a─c)| * |(a─c)| = |(a─d)| * |(a─d)| + |(d─c)| * |(d─c)|; assumption)))

  euclid_sentence "2.13.7"
    "So the (square) on $AC$ alone is less than the (sum of the) squares on $CB$ and $BA$ by twice the rectangle contained by $CB$ and $BD$."
    (step7 : |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|) = |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)|) := by euclid_apply (helper_2_13_step7 a b c d (by euclid_assumption "" (show |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| = |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|); assumption)))

  exact step7
  euclid_conclude_sentence "2.13.8"
    "Thus, in acute-angled triangles, the square on the side subtending the acute angle is less than the (sum of the) squares on the sides containing the acute angle by twice the (rectangle) contained by one of the sides around the acute angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off inside (the triangle) by the perpendicular (straight-line) towards the acute angle. (Which is) the very thing it was required to show."

end Elements.Book2
