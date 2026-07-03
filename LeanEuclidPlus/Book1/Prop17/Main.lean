import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_17 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC →
  ∠ a:b:c + ∠ b:c:a < ∟ + ∟ := by
  euclid_intros
  euclid_intro_sentence "1.17.0"
    "For any triangle,  (the sum of) two angles taken together in any (possible way) is less than two right-angles. Let $ABC$ be a triangle. I say that (the sum of) two angles of triangle $ABC$ taken together in any (possible way) is less than two right-angles. "

  euclid_apply (extend_point BC b c) as d
  euclid_sentence "1.17.1"
    "For let $BC$ have been produced to $D$. "
    (step1 : between b c d) := by sorry

  -- @assumption_valid
  have step2_assumption1 : between b c d := by assumption
  -- @assumption ("the angle $ACD$ is external to triangle $ABC$", between b c d)
  euclid_sentence "1.17.2"
    "And since the angle $ACD$ is external to triangle $ABC$, it is greater than the internal and opposite angle $ABC$ [Prop.~1.16]."
    (step2 : ∠ a:c:d > ∠ a:b:c) := by sorry

  euclid_sentence "1.17.3"
    "Let $ACB$ have been added to both."
    (step3 : ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ a:c:b) := by sorry

  euclid_sentence "1.17.4"
    "Thus, the (sum of the angles) $ACD$ and $ACB$ is greater than the  (sum of the angles) $ABC$ and $BCA$."
    (step4 : ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ b:c:a) := by sorry

  euclid_sentence "1.17.5"
    "But, (the sum of) $ACD$ and $ACB$ is equal to two right-angles [Prop.~1.13]."
    (step5 : ∠ a:c:d + ∠ a:c:b = ∟ + ∟) := by sorry

  euclid_sentence "1.17.6"
    "Thus, (the sum of) $ABC$ and $BCA$ is less than two right-angles."
    (step6 : ∠ a:b:c + ∠ b:c:a < ∟ + ∟) := by sorry

  euclid_sentence "1.17.7"
    "Similarly, we can show that (the sum of) $BAC$ and $ACB$ is also less than two right-angles,"
    (step7 : ∠ b:a:c + ∠ a:c:b < ∟ + ∟) := by sorry

  euclid_sentence "1.17.8"
    "and further (that the sum of) $CAB$ and $ABC$ (is less than two right-angles). "
    (step8 : ∠ c:a:b + ∠ a:b:c < ∟ + ∟) := by sorry

  exact step6
  euclid_conclude_sentence "1.17.9"
    "Thus, for any triangle,  (the sum of) two angles taken together in any (possible way) is less than two right-angles. (Which is) the very thing it was required to show."

end Elements.Book1
