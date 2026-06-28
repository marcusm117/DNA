import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2


set_option systemE.solverTime 30 in
theorem proposition_12 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ (∠ b:a:c : ℝ) > ∟ ∧
  d.onLine CA ∧ between d a c ∧ (∠ b:d:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| =
    |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_intros
  euclid_intro_sentence "2.12.0"
    "In obtuse-angled triangles, the square on the side subtending the obtuse angle is greater than the (sum of the) squares on the sides containing the obtuse angle by twice the (rectangle) contained by one of the sides around the obtuse angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off outside (the triangle) by the perpendicular (straight-line) towards the obtuse angle. Let $ABC$ be an obtuse-angled triangle, having the angle $BAC$ obtuse. And let $BD$ be drawn from point $B$, perpendicular to $CA$ produced [Prop.~1.12]. I say that the square on $BC$ is greater than the (sum of the) squares on $BA$ and $AC$ by twice the rectangle contained by $CA$ and $AD$."

  -- @assumption ("the straight-line $CD$ has been cut, at random, at point $A$", between d a c)
  euclid_sentence "2.12.1"
    "For since the straight-line $CD$ has been cut, at random, at point $A$, the (square) on $DC$ is thus equal to the (sum of the) squares on $CA$ and $AD$, and twice the rectangle contained by $CA$ and $AD$ [Prop.~2.4]."
    (step1 : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|)) := by sorry

  euclid_sentence "2.12.2"
    "Let the (square) on $DB$ be added to both."
    (step2 : |(d─c)| * |(d─c)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|)) := by sorry

  euclid_sentence "2.12.3"
    "Thus, the (sum of the squares) on $CD$ and $DB$ is equal to the (sum of the) squares on $CA$, $AD$, and $DB$, and twice the [rectangle contained] by $CA$ and $AD$."
    (step3 : |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|)) := by sorry

  -- @assumption ("the angle at $D$ (is) a right-angle", ∠ b:d:c = ∟)
  euclid_sentence "2.12.4"
    "But, the (square) on $CB$ is equal to the (sum of the squares) on $CD$ and $DB$. For the angle at $D$ (is) a right-angle [Prop.~1.47]."
    (step4 : |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)|) := by sorry

  euclid_sentence "2.12.5"
    "And the (square) on $AB$ (is) equal to the (sum of the squares) on $AD$ and $DB$ [Prop.~1.47]."
    (step5 : |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)|) := by sorry

  euclid_sentence "2.12.6"
    "Thus, the square on $CB$ is equal to the (sum of the) squares on $CA$ and $AB$, and twice the rectangle contained by $CA$ and $AD$."
    (step6 : |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|)) := by sorry

  euclid_sentence "2.12.7"
    "So the square on $CB$ is greater than the (sum of the) squares on $CA$ and $AB$ by twice the rectangle contained by $CA$ and $AD$."
    (step7 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|)) := by sorry

  exact step7
  euclid_conclude_sentence "2.12.8"
    "Thus, in obtuse-angled triangles, the square on the side subtending the obtuse angle is greater than the (sum of the) squares on the sides containing the obtuse angle by twice the (rectangle) contained by one of the sides around the obtuse angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off outside (the triangle) by the perpendicular (straight-line) towards the obtuse angle. (Which is) the very thing it was required to show."

end Elements.Book2
