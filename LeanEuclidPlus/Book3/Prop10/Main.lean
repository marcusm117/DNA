import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_10 : ∀ (ABC DEF : Circle),
  ABC ≠ DEF →
  ¬ ∃ (p q r : Point),
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    p.onCircle ABC ∧ q.onCircle ABC ∧ r.onCircle ABC ∧
    p.onCircle DEF ∧ q.onCircle DEF ∧ r.onCircle DEF :=
by
  euclid_intros
  euclid_intro_sentence "3.10.0"
    "A circle does not cut a(nother) circle at more than two points."

  have habsurd1 : ¬(sorry) := by
    intro hsuppose1
    euclid_sentence "3.10.1"
      "For, if possible, let the circle $ABC$ cut the circle $DEF$ at more than two points, $B$, $G$, $F$, and $H$."
      (step1 : True) := by sorry

    euclid_sentence "3.10.2"
      "And $BH$ and $BG$ being joined, let them (then) be cut in half at points $K$ and $L$ (respectively)."
      (step2 : True) := by sorry

    euclid_sentence "3.10.3"
      "And $KC$ and $LM$ being drawn at right-angles to $BH$ and $BG$ from $K$ and $L$ (respectively) [Prop.~1.11], let them (then) be drawn through to points $A$ and $E$ (respectively)."
      (step3 : True) := by sorry

    -- @assumption ("in circle $ABC$ some straight-line $AC$ cuts some (other) straight-line $BH$ in half, and at right-angles", TODO)
    euclid_sentence "3.10.4"
      "Therefore, since in circle $ABC$ some straight-line $AC$ cuts some (other) straight-line $BH$ in half, and at right-angles, the center of circle $ABC$ is thus on $AC$ [Prop.~3.1~corr.]."
      (step4 : True) := by sorry

    -- @assumption ("in the same circle $ABC$ some straight-line $NO$ cuts some (other straight-line) $BG$ in half, and at right-angles", TODO)
    euclid_sentence "3.10.5"
      "Again, since in the same circle $ABC$ some straight-line $NO$ cuts some (other straight-line) $BG$ in half, and at right-angles, the center of circle $ABC$ is thus on $NO$ [Prop.~3.1~corr.]."
      (step5 : True) := by sorry

    euclid_sentence "3.10.6"
      "And it was also shown (to be) on $AC$."
      (step6 : True) := by sorry

    euclid_sentence "3.10.7"
      "And the straight-lines $AC$ and $NO$ meet at no other (point) than $P$."
      (step7 : True) := by sorry

    euclid_sentence "3.10.8"
      "Thus, point $P$ is the center of circle $ABC$."
      (step8 : True) := by sorry

    euclid_sentence "3.10.9"
      "So, similarly, we can show that $P$ is also the center of circle $DEF$."
      (step9 : True) := by sorry

    euclid_sentence "3.10.10"
      "Thus, two circles cutting one another, $ABC$ and $DEF$, have the same center $P$."
      (step10 : True) := by sorry

    euclid_sentence "3.10.11"
      "The very thing is impossible [Prop.~3.5]."
      (step11 : False) := by sorry
    exact step11

  euclid_sentence "3.10.12"
    "Thus, a circle does not cut a(nother) circle at more than two points."
    (step12 : True) := by sorry

  -- NOTE: existential conclusion — `exact step12` won't close the goal.
  -- The existential witness + betweenness/construction proof needs manual fixup.
  sorry
  euclid_conclude_sentence "3.10.13"
    "(Which is) the very thing it was required to show."

end Elements.Book3
