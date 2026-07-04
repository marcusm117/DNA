import SystemE
import Book.Prop03
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_20 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC →
  |(b─a)| + |(a─c)| > |(b─c)| ∧
  |(a─b)| + |(b─c)| > |(a─c)| ∧
  |(b─c)| + |(c─a)| > |(a─b)| := by
  euclid_intros
  euclid_intro_sentence "1.20.0"
    "In any triangle, (the sum of) two sides taken together in any (possible way) is greater than the remaining (side). For let $ABC$ be a triangle. I say that in triangle $ABC$ (the sum of) two sides taken together in any (possible way) is greater than the remaining (side). (So), (the sum of) $BA$ and $AC$ (is greater) than $BC$, (the sum of) $AB$ and $BC$ than $AC$, and (the sum of) $BC$ and $CA$ than $AB$. "

  euclid_apply (extend_point_longer AB b a (c─a)) as d'
  euclid_apply (proposition_3 a d' a c AB AC) as d
  euclid_sentence "1.20.1"
    "For let $BA$ have been drawn through to point $D$,"
    (step1 : between b a d) := by sorry

  euclid_sentence "1.20.2"
    "and let $AD$ be made equal to $CA$ [Prop.~1.3],"
    (step2 : |(a─d)| = |(c─a)|) := by sorry

  euclid_apply (line_from_points d c) as DC
  euclid_sentence "1.20.3"
    "and let $DC$ have been joined. "
    (step3 : distinctPointsOnLine d c DC) := by sorry

  -- @assumption_valid
  have step4_assumption1 : |(d─a)| = |(a─c)| := by euclid_finish
  -- @assumption ("$DA$ is equal to $AC$", |(d─a)| = |(a─c)|)
  euclid_sentence "1.20.4"
    "Therefore, since $DA$ is equal to $AC$, the angle $ADC$ is also equal to $ACD$ [Prop.~1.5]."
    (step4 : ∠ a:d:c = ∠ a:c:d) := by sorry

  euclid_sentence "1.20.5"
    "Thus, $BCD$ is greater than $ADC$."
    (step5 : ∠ b:c:d > ∠ a:d:c) := by sorry

  -- @assumption_valid
  have step6_assumption1 : ∠ b:c:d > ∠ b:d:c := by euclid_finish
  -- @assumption ("$DCB$ is a triangle having the angle $BCD$ greater than $BDC$", ∠ b:c:d > ∠ b:d:c)
  euclid_sentence "1.20.6"
    "And since  $DCB$ is a triangle having the angle $BCD$ greater than $BDC$, and the greater angle subtends the greater side [Prop.~1.19], $DB$ is thus greater than $BC$."
    (step6 : |(d─b)| > |(b─c)|) := by sorry

  euclid_sentence "1.20.7"
    "But $DA$ is equal to $AC$."
    (step7 : |(d─a)| = |(a─c)|) := by sorry

  euclid_sentence "1.20.8"
    "Thus, (the sum of) $BA$ and $AC$ is greater than $BC$."
    (step8 : |(b─a)| + |(a─c)| > |(b─c)|) := by sorry

  euclid_sentence "1.20.9"
    "Similarly, we can show that (the sum of) $AB$ and $BC$ is also greater than $CA$,"
    (step9 : |(a─b)| + |(b─c)| > |(a─c)|) := by sorry

  euclid_sentence "1.20.10"
    "and (the sum of) $BC$ and $CA$ than $AB$. "
    (step10 : |(b─c)| + |(c─a)| > |(a─b)|) := by sorry

  exact ⟨step8, step9, step10⟩
  euclid_conclude_sentence "1.20.11"
    "Thus, in any triangle, (the sum of) two sides taken together in any (possible way) is greater than the remaining (side). (Which is) the very thing it was required to show."

end Elements.Book1
