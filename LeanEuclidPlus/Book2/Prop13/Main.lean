import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem proposition_13 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧
  (∠ a:b:c : ℝ) < ∟ ∧ (∠ b:c:a : ℝ) < ∟ ∧ (∠ c:a:b : ℝ) < ∟ ∧
  d.onLine BC ∧ between b d c ∧ (∠ a:d:c : ℝ) = ∟ →
  |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|) =
    |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| := by
  euclid_intros
  euclid_intro_sentence "2.13.0"
    "In acute-angled triangles, the square on the side subtending the acute angle is less than the (sum of the) squares on the sides containing the acute angle by twice the (rectangle) contained by one of the sides around the acute angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off inside (the triangle) by the perpendicular (straight-line) towards the acute angle. Let $ABC$ be an acute-angled triangle, having the angle at (point) $B$ acute. And let $AD$ be drawn from point $A$, perpendicular to $BC$ [Prop.~1.12]. I say that the square on $AC$ is less than the (sum of the) squares on $CB$ and $BA$ by twice the rectangle contained by $CB$ and $BD$."

  -- @assumption ("the straight-line $CB$ has been cut, at random, at (point) $D$", between b d c)
  euclid_sentence "2.13.1"
    "For since the straight-line $CB$ has been cut, at random, at (point) $D$, the (sum of the) squares on $CB$ and $BD$ is thus equal to twice the rectangle contained by $CB$ and $BD$, and the square on $DC$ [Prop.~2.7]."
    (step1 : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| = 2 * (|(c─b)| * |(b─d)|) + |(d─c)| * |(d─c)|) := by sorry

  euclid_sentence "2.13.2"
    "Let the square on $DA$ be added to both."
    (step2 : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| = 2 * (|(c─b)| * |(b─d)|) + |(d─c)| * |(d─c)| + |(d─a)| * |(d─a)|) := by sorry

  euclid_sentence "2.13.3"
    "Thus, the (sum of the) squares on $CB$, $BD$, and $DA$ is equal to twice the rectangle contained by $CB$ and $BD$, and the (sum of the) squares on $AD$ and $DC$."
    (step3 : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| = 2 * (|(c─b)| * |(b─d)|) + |(a─d)| * |(a─d)| + |(d─c)| * |(d─c)|) := by sorry

  -- @assumption ("the angle at (point) $D$ is a right-angle", ∠ a:d:c = ∟)
  euclid_sentence "2.13.4"
    "But, the (square) on $AB$ (is) equal to the (sum of the squares) on $BD$ and $DA$. For the angle at (point) $D$ is a right-angle [Prop.~1.47]."
    (step4 : |(a─b)| * |(a─b)| = |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)|) := by sorry

  euclid_sentence "2.13.5"
    "And the (square) on $AC$ (is) equal to the (sum of the squares) on $AD$ and $DC$ [Prop.~1.47]."
    (step5 : |(a─c)| * |(a─c)| = |(a─d)| * |(a─d)| + |(d─c)| * |(d─c)|) := by sorry

  euclid_sentence "2.13.6"
    "Thus, the (sum of the squares) on $CB$ and $BA$ is equal to the (square) on $AC$, and twice the (rectangle contained) by $CB$ and $BD$."
    (step6 : |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| = |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|)) := by sorry

  euclid_sentence "2.13.7"
    "So the (square) on $AC$ alone is less than the (sum of the) squares on $CB$ and $BA$ by twice the rectangle contained by $CB$ and $BD$."
    (step7 : |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|) = |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)|) := by sorry

  exact step7
  euclid_conclude_sentence "2.13.8"
    "Thus, in acute-angled triangles, the square on the side subtending the acute angle is less than the (sum of the) squares on the sides containing the acute angle by twice the (rectangle) contained by one of the sides around the acute angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off inside (the triangle) by the perpendicular (straight-line) towards the acute angle. (Which is) the very thing it was required to show."

end Elements.Book2
