import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_16 : ∀ (a b d e : Point) (ABC : Circle) (AE : Line),
    d.isCentre ABC ∧
    a.onCircle ABC ∧ b.onCircle ABC ∧ between a d b ∧
    distinctPointsOnLine a e AE ∧
    ∠ e:a:b = ∟ →
    ((∃ p : Point, p.onLine AE ∧ p.onCircle ABC) ∧ ¬ AE.intersectsCircle ABC) ∧
    (∀ (FA : Line), a.onLine FA → FA ≠ AE → FA.intersectsCircle ABC) :=
by
  euclid_intros
  euclid_intro_sentence "3.16.0"
    "A (straight-line) drawn at right-angles to the diameter of a circle, from its end, will fall outside the circle. And another straight-line cannot be inserted into the space between the (aforementioned) straight-line and the circumference. And the angle of the semi-circle is greater than any acute rectilinear angle whatsoever, and the remaining (angle is) less (than any acute rectilinear angle). Let $ABC$ be a circle around the center $D$ and the diameter $AB$. I say that the (straight-line) drawn from $A$, at right-angles to $AB$ [Prop~1.11], from its end, will fall outside the circle."

  have habsurd1 : ¬(sorry) := by
    intro hsuppose1
    euclid_sentence "3.16.1"
      "For (if) not (then), if possible, let it fall inside, like $CA$ (in the figure),"
      (step1 : True) := by sorry

    euclid_sentence "3.16.2"
      "and let $DC$ be joined."
      (step2 : True) := by sorry

    -- @assumption ("$DA$ is equal to $DC$", TODO)
    euclid_sentence "3.16.3"
      "Since $DA$ is equal to $DC$, angle $DAC$ is also equal to angle $ACD$ [Prop.~1.5]."
      (step3 : True) := by sorry

    euclid_sentence "3.16.4"
      "And $DAC$ (is) a right-angle."
      (step4 : True) := by sorry

    euclid_sentence "3.16.5"
      "Thus, $ACD$ (is) also a right-angle."
      (step5 : True) := by sorry

    euclid_sentence "3.16.6"
      "So, in triangle $ACD$, the two angles $DAC$ and $ACD$ are equal to two right-angles."
      (step6 : True) := by sorry

    euclid_sentence "3.16.7"
      "The very thing is impossible [Prop.~1.17]."
      (step7 : False) := by sorry
    exact step7

  euclid_sentence "3.16.8"
    "Thus, the (straight-line) drawn from point $A$, at right-angles to $BA$, will not fall inside the circle."
    (step8 : True) := by sorry

  euclid_sentence "3.16.9"
    "So, similarly, we can show that neither (will it fall) on the circumference."
    (step9 : True) := by sorry

  euclid_sentence "3.16.10"
    "Thus, (it will fall) outside (the circle)."
    (step10 : True) := by sorry

  euclid_sentence "3.16.11"
    "Let it fall like $AE$ (in the figure)."
    (step11 : True) := by sorry

  euclid_wts "3.16.12"
    "So, I say that another straight-line cannot be inserted into the space between the straight-line $AE$ and the circumference $CHA$."

  have habsurd2 : ¬(sorry) := by
    intro hsuppose2
    euclid_sentence "3.16.13"
      "For, if possible, let it be inserted like $FA$ (in the figure),"
      (step13 : True) := by sorry

    euclid_sentence "3.16.14"
      "and let $DG$ be drawn from point $D$, perpendicular to $FA$ [Prop.~1.12]."
      (step14 : True) := by sorry

    -- @assumption ("$AGD$ is a right-angle", TODO)
    -- @assumption ("$DAG$ (is) less than a right-angle", TODO)
    euclid_sentence "3.16.15"
      "And since $AGD$ is a right-angle, and $DAG$ (is) less than a right-angle, $AD$ (is) thus greater than $DG$ [Prop.~1.19]."
      (step15 : True) := by sorry

    euclid_sentence "3.16.16"
      "And $DA$ (is) equal to $DH$."
      (step16 : True) := by sorry

    euclid_sentence "3.16.17"
      "Thus, $DH$ (is) greater than $DG$, the lesser than the greater."
      (step17 : True) := by sorry

    euclid_sentence "3.16.18"
      "The very thing is impossible."
      (step18 : False) := by sorry
    exact step18

  euclid_sentence "3.16.19"
    "Thus, another straight-line cannot be inserted into the space between the straight-line ($AE$) and the circumference."
    (step19 : True) := by sorry

  euclid_wts "3.16.20"
    "And I also say that the semi-circular angle contained by the straight-line $BA$ and the circumference $CHA$ is greater than any acute rectilinear angle whatsoever, and the remaining (angle) contained by the circumference $CHA$ and the straight-line $AE$ is less than any acute rectilinear angle whatsoever."

  euclid_sentence "3.16.21"
    "For if any rectilinear angle is greater than the (angle) contained by the straight-line $BA$ and the circumference $CHA$, or less than the (angle) contained by the circumference $CHA$ and the straight-line $AE$, (then) a straight-line can be inserted into the space between the circumference $CHA$ and the straight-line $AE$---anything which will make (an angle) contained by straight-lines greater than the angle contained by the straight-line $BA$ and the circumference $CHA$, or less than the (angle) contained by the circumference $CHA$ and the straight-line $AE$."
    (step21 : True) := by sorry

  euclid_sentence "3.16.22"
    "But (such a straight-line) cannot be inserted."
    (step22 : True) := by sorry

  euclid_sentence "3.16.23"
    "Thus, an acute (angle) contained by straight-lines cannot be greater than the angle contained by the straight-line $BA$ and the circumference $CHA$,"
    (step23 : True) := by sorry

  euclid_sentence "3.16.24"
    "neither (can it be) less than the (angle) contained by the circumference $CHA$ and the straight-line $AE$."
    (step24 : True) := by sorry

  euclid_sentence "3.16.25"
    "So, from this, (it is) manifest that a (straight-line) drawn at right-angles to the diameter of a circle, from its extremity, touches the circle [and that the straight-line touches the circle at a single point, inasmuch as it was also shown that a (straight-line) meeting (the circle) at two (points) falls inside it [Prop.~3.2]\\,]."
    (step25 : True) := by sorry

  -- NOTE: existential conclusion — `exact step25` won't close the goal.
  -- The existential witness + betweenness/construction proof needs manual fixup.
  sorry
  euclid_conclude_sentence "3.16.26"
    "(Which is) the very thing it was required to show."

end Elements.Book3
