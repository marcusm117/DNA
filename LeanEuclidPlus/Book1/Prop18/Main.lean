import SystemE
import Book.Prop03
import Book.Prop05
import Book.Prop16
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_18 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─c)| > |(a─b)|) →
  (∠ a:b:c > ∠ b:c:a) := by
  euclid_intros
  euclid_intro_sentence "1.18.0"
    "In any triangle, the greater side subtends the greater angle. For let $ABC$ be a triangle having side $AC$ greater than $AB$. I say that angle $ABC$ is also greater than $BCA$. "

  euclid_apply (proposition_3 a c a b AC AB) as d
  euclid_sentence "1.18.1"
    "For since $AC$ is greater than $AB$, let $AD$ be made equal to $AB$  [Prop.~1.3],"
    (step1 : |(a─d)| = |(a─b)|) := by sorry

  euclid_apply (line_from_points b d) as BD
  euclid_sentence "1.18.2"
    "and let $BD$ have been joined. "
    (step2 : distinctPointsOnLine b d BD) := by sorry

  -- @assumption_valid
  have step3_assumption1 : between a d c := by assumption
  -- @assumption ("angle $ADB$ is external to triangle $BCD$", between a d c)
  euclid_sentence "1.18.3"
    "And since angle $ADB$ is external to triangle $BCD$, it is greater than the internal and opposite (angle) $DCB$ [Prop.~1.16]."
    (step3 : ∠ a:d:b > ∠ d:c:b) := by sorry

  -- @assumption_valid
  have step4_assumption1 : |(a─b)| = |(a─d)| := by linarith
  -- @assumption ("$AB$ is also equal to side $AD$", |(a─b)| = |(a─d)|)
  euclid_sentence "1.18.4"
    "But $ADB$ (is) equal to $ABD$, since side $AB$ is also equal to side $AD$ [Prop.~1.5]."
    (step4 : ∠ a:d:b = ∠ a:b:d) := by sorry

  euclid_sentence "1.18.5"
    "Thus, $ABD$ is also greater than $ACB$."
    (step5 : ∠ a:b:d > ∠ b:c:a) := by sorry

  euclid_sentence "1.18.6"
    "Thus, $ABC$ is much greater than  $ACB$. "
    (step6 : ∠ a:b:c > ∠ b:c:a) := by sorry

  exact step6
  euclid_conclude_sentence "1.18.7"
    "Thus, in any triangle, the greater side subtends the greater angle. (Which is) the very thing  it was required to show."

end Elements.Book1
