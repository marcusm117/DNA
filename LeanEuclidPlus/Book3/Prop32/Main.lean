import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_32 : ∀ (b a d c e f : Point) (ABCD : Circle) (EF BD : Line),
  b.onLine EF ∧ b.onCircle ABCD ∧ ¬ EF.intersectsCircle ABCD ∧
  e.onLine EF ∧ f.onLine EF ∧ between e b f ∧
  b.onLine BD ∧ d.onCircle ABCD ∧ d.onLine BD ∧ b ≠ d ∧
  a.onCircle ABCD ∧ c.onCircle ABCD ∧
  a.opposingSides f BD ∧ c.opposingSides e BD →
  ∠ f:b:d = ∠ b:a:d ∧ ∠ e:b:d = ∠ d:c:b :=
by
  euclid_intros
  euclid_intro_sentence "3.32.0"
    "If some straight-line touches a circle, and some (other) straight-line is drawn across, from the point of contact into the circle, cutting the circle (in two), (then) those angles the (straight-line) makes with the tangent will be equal to the angles in the alternate segments of the circle. For let some straight-line $EF$ touch the circle $ABCD$ at the point $B$, and let some (other) straight-line $BD$ be drawn from point $B$ into the circle $ABCD$, cutting it (in two). I say that the angles $BD$ makes with the tangent $EF$ will be equal to the angles in the alternate segments of the circle. That is to say, that angle $FBD$ is equal to the angle constructed in segment $BAD$, and angle $EBD$ is equal to the angle constructed in segment $DCB$."

  euclid_apply (line_from_points b a) as BA
  euclid_sentence "3.32.1"
    "For let $BA$ be drawn from $B$, at right-angles to $EF$ [Prop.~1.11]."
    (step1 : distinctPointsOnLine b a BA ∧ ∠ a:b:f = ∟) := by sorry

  -- orchestrator-given-as-construction: c.onCircle ABCD is in the signature hypothesis; the
  -- construction sentence "let C be taken at random" asserts this (Prop22.step1 parallel — Rule 0).
  euclid_sentence "3.32.2"
    "And let the point $C$ be taken at random on the circumference $BD$."
    (step2 : c.onCircle ABCD) := by sorry

  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points d c) as DC
  euclid_apply (line_from_points c b) as CB
  euclid_sentence "3.32.3"
    "And let $AD$, $DC$, and $CB$ be joined."
    (step3 : distinctPointsOnLine a d AD ∧ distinctPointsOnLine d c DC ∧ distinctPointsOnLine c b CB) := by sorry

  -- @assumption ("some straight-line $EF$ touches the circle $ABCD$ at point $B$", b.onLine EF ∧ b.onCircle ABCD ∧ ¬EF.intersectsCircle ABCD)
  -- @assumption ("$BA$ has been drawn from the point of contact, at right-angles to the tangent", distinctPointsOnLine b a BA ∧ ∠ a:b:f = ∟)
  -- orchestrator-forall: step4 is ∀-typed, mirroring proposition_19's conclusion directly.
  -- Wireable: helpers receive it as a value (not auto-applied to the Main goal); no forallE wiring issue.
  euclid_sentence "3.32.4"
    "And since some straight-line $EF$ touches the circle $ABCD$ at point $B$, and $BA$ has been drawn from the point of contact, at right-angles to the tangent, the center of circle $ABCD$ is thus on $BA$ [Prop.~3.19]."
    (step4 : ∀ o : Point, o.isCentre ABCD → o.onLine BA) := by sorry

  euclid_sentence "3.32.5"
    "Thus, $BA$ is a diameter of circle $ABCD$."
    (step5 : ∃ o : Point, o.isCentre ABCD ∧ between a o b ∧ a.onCircle ABCD ∧ b.onCircle ABCD) := by sorry

  euclid_sentence "3.32.6"
    "Thus, angle $ADB$, being in a semi-circle, is a right-angle [Prop.~3.31]."
    (step6 : ∠ a:d:b = ∟) := by sorry

  euclid_sentence "3.32.7"
    "Thus, the remaining angles (of triangle $ADB$) $BAD$ and $ABD$ are equal to one right-angle [Prop.~1.32]."
    (step7 : ∠ b:a:d + ∠ a:b:d = ∟) := by sorry

  -- orchestrator-restate-step: ∠a:b:f = ∟ is step1's second conjunct; Euclid re-states it here
  -- to set up the comparison ABF = ADB + DAB. Faithful repetition, not vacuous (Rule 3).
  euclid_sentence "3.32.8"
    "And $ABF$ is also a right-angle."
    (step8 : ∠ a:b:f = ∟) := by sorry

  euclid_sentence "3.32.9"
    "Thus, $ABF$ is equal to $BAD$ and $ABD$."
    (step9 : ∠ a:b:f = ∠ b:a:d + ∠ a:b:d) := by sorry

  euclid_sentence "3.32.10"
    "Let $ABD$ be subtracted from both."
    (step10 : ∠ a:b:f - ∠ a:b:d = ∠ b:a:d) := by sorry

  euclid_sentence "3.32.11"
    "Thus, the remaining angle $DBF$ is equal to the angle $BAD$ in the alternate segment of the circle."
    (step11 : ∠ f:b:d = ∠ b:a:d) := by sorry

  -- @assumption ("$ABCD$ is a quadrilateral in a circle", a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD)
  euclid_sentence "3.32.12"
    "And since $ABCD$ is a quadrilateral in a circle, (the sum of) its opposite angles is equal to two right-angles [Prop.~3.22]."
    (step12 : ∠ b:a:d + ∠ b:c:d = ∟ + ∟) := by sorry

  euclid_sentence "3.32.13"
    "And $DBF$ and $DBE$ is also equal to two right-angles [Prop.~1.13]."
    (step13 : ∠ f:b:d + ∠ e:b:d = ∟ + ∟) := by sorry

  -- @assumption ("$BAD$ was shown (to be) equal to $DBF$", ∠ f:b:d = ∠ b:a:d)
  euclid_sentence "3.32.14"
    "Thus, $DBF$ and $DBE$ is equal to $BAD$ and $BCD$, of which $BAD$ was shown (to be) equal to $DBF$."
    (step14 : ∠ f:b:d + ∠ e:b:d = ∠ b:a:d + ∠ b:c:d) := by sorry

  euclid_sentence "3.32.15"
    "Thus, the remaining (angle) $DBE$ is equal to the angle $DCB$ in the alternate segment $DCB$ of the circle."
    (step15 : ∠ e:b:d = ∠ d:c:b) := by sorry

  exact ⟨step11, step15⟩
  euclid_conclude_sentence "3.32.16"
    "Thus, if some straight-line touches a circle, and some (other) straight-line is drawn across, from the point of contact into the circle, cutting the circle (in two), (then) those angles the (straight-line) makes with the tangent will be equal to the angles in the alternate segments of the circle. (Which is) the very thing it was required to show."

end Elements.Book3
