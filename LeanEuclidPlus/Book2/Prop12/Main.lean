import SystemE
import Book1.Prop12.Main
import Book2.Prop12.step1
import Book2.Prop12.step2
import Book2.Prop12.step3
import Book2.Prop12.step4
import Book2.Prop12.step5
import Book2.Prop12.step6
import Book2.Prop12.step7
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2


theorem proposition_12 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ (∠ b:a:c : ℝ) > ∟ ∧
  d.onLine CA ∧ between d a c ∧ (∠ b:d:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| =
    |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_12 c a b CA) as d0
  euclid_intro_sentence "2.12.0"
    "In obtuse-angled triangles, the square on the side subtending the obtuse angle is greater than the (sum of the) squares on the sides containing the obtuse angle by twice the (rectangle) contained by one of the sides around the obtuse angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off outside (the triangle) by the perpendicular (straight-line) towards the obtuse angle. Let $ABC$ be an obtuse-angled triangle, having the angle $BAC$ obtuse. And let $BD$ be drawn from point $B$, perpendicular to $CA$ produced [Prop.~1.12]. I say that the square on $BC$ is greater than the (sum of the) squares on $BA$ and $AC$ by twice the rectangle contained by $CA$ and $AD$."

  -- @assumption_valid
  have step1_assumption1 : between d a c := by assumption
  -- @assumption ("the straight-line $CD$ has been cut, at random, at point $A$", between d a c)
  euclid_sentence "2.12.1"
    "For since the straight-line $CD$ has been cut, at random, at point $A$, the (square) on $DC$ is thus equal to the (sum of the) squares on $CA$ and $AD$, and twice the rectangle contained by $CA$ and $AD$ [Prop.~2.4]."
    (step1 : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|)) := by euclid_apply (helper_2_12_step1 d a c CA (by euclid_assumption "" (show d.onLine CA; assumption)) (by euclid_assumption "" (show a.onLine CA; assumption)) (by euclid_assumption "" (show c.onLine CA; assumption)) (by euclid_assumption "the straight-line $CD$ has been cut, at random, at point $A$" (show between d a c; assumption)))

  euclid_sentence "2.12.2"
    "Let the (square) on $DB$ be added to both."
    (step2 : |(d─c)| * |(d─c)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|)) := by euclid_apply (helper_2_12_step2 d c a b (by euclid_assumption "" (show |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|); assumption)))

  euclid_sentence "2.12.3"
    "Thus, the (sum of the squares) on $CD$ and $DB$ is equal to the (sum of the) squares on $CA$, $AD$, and $DB$, and twice the [rectangle contained] by $CA$ and $AD$."
    (step3 : |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|)) := by euclid_apply (helper_2_12_step3 c d a b (by euclid_assumption "" (show |(d─c)| * |(d─c)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|); assumption)))

  -- @assumption_valid
  have step4_assumption1 : ∠ b:d:c = ∟ := by assumption
  -- @assumption ("the angle at $D$ (is) a right-angle", ∠ b:d:c = ∟)
  euclid_sentence "2.12.4"
    "But, the (square) on $CB$ is equal to the (sum of the squares) on $CD$ and $DB$. For the angle at $D$ (is) a right-angle [Prop.~1.47]."
    (step4 : |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)|) := by euclid_apply (helper_2_12_step4 a b c d AB BC CA (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CA; assumption)) (by euclid_assumption "" (show a.onLine CA; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ CA; assumption)) (by euclid_assumption "" (show CA ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine CA; assumption)) (by euclid_assumption "" (show between d a c; assumption)) (by euclid_assumption "the angle at $D$ (is) a right-angle" (show ∠ b:d:c = ∟; assumption)))

  euclid_sentence "2.12.5"
    "And the (square) on $AB$ (is) equal to the (sum of the squares) on $AD$ and $DB$ [Prop.~1.47]."
    (step5 : |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)|) := by euclid_apply (helper_2_12_step5 a b c d AB BC CA (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CA; assumption)) (by euclid_assumption "" (show a.onLine CA; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ CA; assumption)) (by euclid_assumption "" (show CA ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine CA; assumption)) (by euclid_assumption "" (show between d a c; assumption)) (by euclid_assumption "" (show ∠ b:d:c = ∟; assumption)))

  euclid_sentence "2.12.6"
    "Thus, the square on $CB$ is equal to the (sum of the) squares on $CA$ and $AB$, and twice the rectangle contained by $CA$ and $AD$."
    (step6 : |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|)) := by euclid_apply (helper_2_12_step6 a b c d (by euclid_assumption "" (show |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|); assumption)) (by euclid_assumption "" (show |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)|; assumption)) (by euclid_assumption "" (show |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)|; assumption)))

  euclid_sentence "2.12.7"
    "So the square on $CB$ is greater than the (sum of the) squares on $CA$ and $AB$ by twice the rectangle contained by $CA$ and $AD$."
    (step7 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|)) := by euclid_apply (helper_2_12_step7 a b c d (by euclid_assumption "" (show |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|); assumption)))

  apply step7
  euclid_conclude_sentence "2.12.8"
    "Thus, in obtuse-angled triangles, the square on the side subtending the obtuse angle is greater than the (sum of the) squares on the sides containing the obtuse angle by twice the (rectangle) contained by one of the sides around the obtuse angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off outside (the triangle) by the perpendicular (straight-line) towards the obtuse angle. (Which is) the very thing it was required to show."

end Elements.Book2
