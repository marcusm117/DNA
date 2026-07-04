import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_19 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c > ∠ b:c:a) →
  (|(a─c)| > |(a─b)|) := by
  euclid_intros
  euclid_intro_sentence "1.19.0"
    "In any triangle, the greater angle is subtended by the greater side. Let $ABC$ be a triangle having the angle $ABC$ greater than $BCA$. I say that side $AC$ is also greater than side $AB$. "

  euclid_sentence "1.19.1"
    "For if not, $AC$ is certainly either equal to, or less than, $AB$."
    (step1 : ¬(|(a─c)| > |(a─b)|) → (|(a─c)| = |(a─b)| ∨ |(a─c)| < |(a─b)|)) := by sorry

  euclid_wts "1.19.2"
    "In fact, $AC$ is not equal to $AB$."
  have hne : |(a─c)| ≠ |(a─b)| := by
    intro h_eq
    euclid_sentence "1.19.3"
      "For then angle $ABC$  would also have been equal to $ACB$ [Prop.~1.5]."
      (step3 : ∠ a:b:c = ∠ b:c:a) := by sorry
    euclid_sentence "1.19.4"
      "But it is not."
      (step4 : False) := by sorry
    exact step4

  euclid_sentence "1.19.5"
    "Thus, $AC$ is not equal to $AB$."
    (step5 : |(a─c)| ≠ |(a─b)|) := by sorry

  euclid_wts "1.19.6"
    "Neither, indeed, is $AC$ less than $AB$."
  have hnlt : ¬(|(a─c)| < |(a─b)|) := by
    intro h_lt
    euclid_sentence "1.19.7"
      "For then angle $ABC$ would also have been less than $ACB$ [Prop.~1.18]."
      (step7 : ∠ a:b:c < ∠ b:c:a) := by sorry
    euclid_sentence "1.19.8"
      "But it is not."
      (step8 : False) := by sorry
    exact step8

  euclid_sentence "1.19.9"
    "Thus, $AC$ is not less than $AB$."
    (step9 : ¬(|(a─c)| < |(a─b)|)) := by sorry

  -- @assumption ("($AC$) is    not equal (to $AB$)", |(a─c)| ≠ |(a─b)|)
  euclid_sentence "1.19.10"
    "But it was  shown that ($AC$) is    not equal (to $AB$) either."
    (step10 : |(a─c)| ≠ |(a─b)|) := by sorry

  euclid_sentence "1.19.11"
    "Thus, $AC$  is greater than $AB$."
    (step11 : |(a─c)| > |(a─b)|) := by sorry

  exact step11
  euclid_conclude_sentence "1.19.12"
    "Thus, in any triangle, the greater angle is subtended by the greater side. (Which is) the very thing it was required to show."

end Elements.Book1
