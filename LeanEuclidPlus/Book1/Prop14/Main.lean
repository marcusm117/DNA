import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_14 : ∀ (a b c d : Point) (AB BC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ distinctPointsOnLine b d BD ∧ (c.opposingSides d AB) ∧
  (∠ a:b:c + ∠ a:b:d) = ∟ + ∟ →
  BC = BD := by
  euclid_intros
  euclid_intro_sentence "1.14.0"
    "If two straight-lines, not lying on the same side,  make adjacent angles (whose sum is) equal to two right-angles  with some straight-line, at a point on it, then the two straight-lines will be straight-on (with respect) to one another. For let two straight-lines $BC$ and $BD$, not lying on the same side,  make adjacent angles $ABC$ and $ABD$ (whose sum is) equal to two right-angles with some straight-line $AB$, at the point $B$ on it. I say that $BD$ is  straight-on with respect to $CB$. "
  -- Euclid argues by contradiction: suppose BD is not straight-on to CB (BC ≠ BD).
  have habsurd : ¬ (BC ≠ BD) := by
    intro hne
    euclid_apply (extend_point BC c b) as e
    euclid_sentence "1.14.1"
      "For if $BD$ is not straight-on to $BC$ then let $BE$ be straight-on to $CB$. "
      (step1 : between c b e) := by sorry

    -- @assumption ("since the straight-line $AB$ stands on the straight-line $CBE$", between c b e)
    euclid_sentence "1.14.2"
      "Therefore, since the straight-line $AB$ stands on the straight-line $CBE$, the (sum of the) angles $ABC$ and $ABE$ is thus equal to two right-angles [Prop.~1.13]."
      (step2 : ∠ a:b:c + ∠ a:b:e = ∟ + ∟) := by sorry

    euclid_sentence "1.14.3"
      "But (the sum of) $ABC$ and $ABD$ is also equal to two right-angles."
      (step3 : ∠ a:b:c + ∠ a:b:d = ∟ + ∟) := by sorry

    euclid_sentence "1.14.4"
      "Thus,  (the sum of angles) $CBA$ and $ABE$ is equal to (the sum of angles) $CBA$ and $ABD$ [C.N.~1]."
      (step4 : ∠ c:b:a + ∠ a:b:e = ∠ c:b:a + ∠ a:b:d) := by sorry

    euclid_sentence "1.14.5"
      "Let (angle) $CBA$ have been subtracted from both."
      (step5 : ∠ a:b:e = ∠ a:b:d) := by sorry

    euclid_sentence "1.14.6"
      "Thus, the remainder $ABE$ is equal to the remainder $ABD$ [C.N.~3], the lesser to the greater."
      (step6 : ∠ a:b:e = ∠ a:b:d) := by sorry

    euclid_sentence "1.14.7"
      "The very thing is impossible."
      (step7 : False) := by sorry

    exact step7

  euclid_conclude_sentence "1.14.8"
    "Thus, $BE$ is not straight-on with respect to $CB$."
  euclid_conclude_sentence "1.14.9"
    "Similarly, we can show that neither (is) any other (straight-line)   than $BD$."
  euclid_sentence "1.14.10"
    "Thus, $CB$ is straight-on with respect to $BD$. "
    (step10 : BC = BD) := by sorry

  exact step10
  euclid_conclude_sentence "1.14.11"
    "Thus, if two straight-lines, not lying on the same side,  make adjacent angles (whose sum is) equal to two right-angles with some straight-line, at a point on it, then the two straight-lines will be straight-on (with respect) to one another. (Which is) the very thing it was required to show."

end Elements.Book1
