import SystemE
import Book.Prop01
import Book.Prop09
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_10 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ d : Point, (between a d b) ∧ (|(a─d)| = |(d─b)|) := by
  euclid_intros
  euclid_intro_sentence "1.10.0"
    "To cut a given finite straight-line in half. Let $AB$ be the given finite straight-line. So it is required to cut the finite straight-line $AB$ in half. "

  euclid_apply (proposition_1 a b AB) as c
  euclid_apply (line_from_points c a) as AC
  euclid_apply (line_from_points c b) as BC
  euclid_sentence "1.10.1"
    "Let the equilateral triangle $ABC$ have been constructed upon  ($AB$) [Prop.~1.1],"
    (step1 : formTriangle a b c AB BC AC ∧ |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|) := by sorry

  euclid_apply (proposition_9' c a b AC BC) as d'
  euclid_apply (line_from_points c d') as CD
  euclid_apply (intersection_lines CD AB) as d
  euclid_sentence "1.10.2"
    "and let the angle $ACB$ have been cut in half by the straight-line $CD$ [Prop.~1.9]."
    (step2 : ∠ a:c:d = ∠ b:c:d) := by sorry

  euclid_sentence "1.10.3"
    "I say that the straight-line $AB$ has been cut in half at  point $D$. "
    (step3 : between a d b ∧ |(a─d)| = |(d─b)|) := by sorry

  -- @assumption ("$AC$ is equal to $CB$", |(a─c)| = |(c─b)|)
  -- @assumption ("$CD$ (is) common", |(c─d)| = |(c─d)|)
  euclid_sentence "1.10.4"
    "For since $AC$ is equal to $CB$, and $CD$ (is) common, the two (straight-lines) $AC$, $CD$ are equal to the two (straight-lines) $BC$, $CD$, respectively."
    (step4 : |(a─c)| = |(b─c)| ∧ |(c─d)| = |(c─d)|) := by sorry

  -- recalls the construction bisection (step2) for use in [Prop.~1.4]
  euclid_sentence "1.10.5"
    "And the angle $ACD$ is equal to the angle $BCD$."
    (step5 : ∠ a:c:d = ∠ b:c:d) := by sorry

  euclid_sentence "1.10.6"
    "Thus, the base $AD$ is equal to the base $BD$ [Prop.~1.4]."
    (step6 : |(a─d)| = |(b─d)|) := by sorry

  exact ⟨d, step3⟩
  euclid_conclude_sentence "1.10.7"
    "Thus, the given finite straight-line $AB$ has been cut in half at  (point) $D$.  (Which is) the very thing it was required to do."

end Elements.Book1
