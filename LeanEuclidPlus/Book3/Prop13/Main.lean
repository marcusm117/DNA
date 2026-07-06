import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_13 : ∀ (ABDC EBFD : Circle),
  ABDC ≠ EBFD ∧ (∃ p : Point, p.onCircle ABDC ∧ p.onCircle EBFD) ∧ ¬ ABDC.intersectsCircle EBFD →
  ∀ (p q : Point), p.onCircle ABDC ∧ p.onCircle EBFD ∧ q.onCircle ABDC ∧ q.onCircle EBFD → p = q :=
by
  euclid_intros
  euclid_intro_sentence "3.13.0"
    "A circle does not touch a(nother) circle at more than one point, whether they touch internally or externally."

  have habsurd1 : ¬(sorry) := by
    intro hsuppose1
    euclid_sentence "3.13.1"
      "For, if possible, let circle $ABDC$$^{\\,\\dag}$ touch circle $EBFD$---first of all, internally---at more than one point, $D$ and $B$."
      (step1 : True) := by sorry

    euclid_sentence "3.13.2"
      "And let the center $G$ of circle $ABDC$ be found [Prop.~3.1],"
      (step2 : True) := by sorry

    euclid_sentence "3.13.3"
      "and (the center) $H$ of $EBFD$ [Prop.~3.1]."
      (step3 : True) := by sorry

    euclid_sentence "3.13.4"
      "Thus, the (straight-line) joining $G$ and $H$ will fall on $B$ and $D$ [Prop.~3.11]."
      (step4 : True) := by sorry

    euclid_sentence "3.13.5"
      "Let it fall like $BGHD$ (in the figure)."
      (step5 : True) := by sorry

    -- @assumption ("point $G$ is the center of circle $ABDC$", TODO)
    euclid_sentence "3.13.6"
      "And since point $G$ is the center of circle $ABDC$, $BG$ is equal to $GD$."
      (step6 : True) := by sorry

    euclid_sentence "3.13.7"
      "Thus, $BG$ (is) greater than $HD$."
      (step7 : True) := by sorry

    euclid_sentence "3.13.8"
      "Thus, $BH$ (is) much greater than $HD$."
      (step8 : True) := by sorry

    -- @assumption ("point $H$ is the center of circle $EBFD$", TODO)
    euclid_sentence "3.13.9"
      "Again, since point $H$ is the center of circle $EBFD$, $BH$ is equal to $HD$."
      (step9 : True) := by sorry

    -- @assumption ("it was also shown (to be) much greater than it", TODO)
    euclid_sentence "3.13.10"
      "But it was also shown (to be) much greater than it. The very thing (is) impossible."
      (step10 : False) := by sorry
    exact step10

  euclid_sentence "3.13.11"
    "Thus, a circle does not touch a(nother) circle internally at more than one point."
    (step11 : True) := by sorry

  euclid_wts "3.13.12"
    "So, I say that neither (does it touch) externally (at more than one point)."

  have habsurd2 : ¬(sorry) := by
    intro hsuppose2
    euclid_sentence "3.13.13"
      "For, if possible, let circle $ACK$ touch circle $ABDC$ externally at more than one point, $A$ and $C$."
      (step13 : True) := by sorry

    euclid_sentence "3.13.14"
      "And let $AC$ be joined."
      (step14 : True) := by sorry

    -- @assumption ("two points, $A$ and $C$, be taken at random on the circumference of each of the circles $ABDC$ and $ACK$", TODO)
    euclid_sentence "3.13.15"
      "Therefore, since two points, $A$ and $C$, be taken at random on the circumference of each of the circles $ABDC$ and $ACK$, the straight-line joining the points will fall inside each (circle) [Prop.~3.2]."
      (step15 : True) := by sorry

    euclid_sentence "3.13.16"
      "But, it fell inside $ABDC$, and outside $ACK$ [Def.~3.3]."
      (step16 : True) := by sorry

    euclid_sentence "3.13.17"
      "The very thing (is) absurd."
      (step17 : False) := by sorry
    exact step17

  euclid_sentence "3.13.18"
    "Thus, a circle does not touch a(nother) circle externally at more than one point."
    (step18 : True) := by sorry

  euclid_sentence "3.13.19"
    "And it was shown that neither (does it) internally."
    (step19 : True) := by sorry

  -- NOTE: existential conclusion — `exact step19` won't close the goal.
  -- The existential witness + betweenness/construction proof needs manual fixup.
  sorry
  euclid_conclude_sentence "3.13.20"
    "Thus, a circle does not touch a(nother) circle at more than one point, whether they touch internally or externally. (Which is) the very thing it was required to show."

end Elements.Book3
