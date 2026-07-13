import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_31 : ∀ (a b c d e : Point) (ABCD : Circle) (AC BD : Line),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
  e.isCentre ABCD ∧
  between b e c ∧
  distinctPointsOnLine a c AC ∧
  distinctPointsOnLine b d BD ∧
  b.opposingSides d AC ∧
  a.opposingSides c BD →
  ∠ b:a:c = ∟ ∧ ∠ a:b:c < ∟ ∧ ∠ a:d:c > ∟ :=
by
  euclid_intros
  euclid_intro_sentence "3.31.0"
    "In a circle, the angle in a semi-circle is a right-angle, and that in a greater segment (is) less than a right-angle, and that in a lesser segment (is) greater than a right-angle. And, further, the angle of a segment greater (than a semi-circle) is greater than a right-angle, and the angle of a segment less (than a semi-circle) is less than a right-angle. Let $ABCD$ be a circle, and let $BC$ be its diameter, and $E$ its center. And let $BA$, $AC$, $AD$, and $DC$ be joined. I say that the angle $BAC$ in the semi-circle $BAC$ is a right-angle, and the angle $ABC$ in the segment $ABC$, (which is) greater than a semi-circle, is less than a right-angle, and the angle $ADC$ in the segment $ADC$, (which is) less than a semi-circle, is greater than a right-angle."

  have hAE0_ex : ∃ AE0 : Line, distinctPointsOnLine a e AE0 := by sorry
  obtain ⟨AE0, hAE0⟩ := hAE0_ex
  have hf_ex : ∃ f : Point, between b a f := by sorry
  obtain ⟨f, hf⟩ := hf_ex
  euclid_sentence "3.31.1"
    "Let $AE$ be joined, and let $BA$ be drawn through to $F$."
    (step1 : distinctPointsOnLine a e AE0 ∧ between b a f) := by sorry

  -- @assumption ("$BE$ is equal to $EA$", |(b─e)| = |(e─a)|)
  euclid_sentence "3.31.2"
    "And since $BE$ is equal to $EA$, angle $ABE$ is also equal to $BAE$ [Prop.~1.5]."
    (step2 : ∠ a:b:e = ∠ b:a:e) := by sorry

  -- @assumption ("$CE$ is equal to $EA$", |(c─e)| = |(e─a)|)
  euclid_sentence "3.31.3"
    "Again, since $CE$ is equal to $EA$, $ACE$ is also equal to $CAE$ [Prop.~1.5]."
    (step3 : ∠ a:c:e = ∠ c:a:e) := by sorry

  euclid_sentence "3.31.4"
    "Thus, the whole (angle) $BAC$ is equal to the two (angles) $ABC$ and $ACB$."
    (step4 : ∠ b:a:c = ∠ a:b:c + ∠ a:c:b) := by sorry

  euclid_sentence "3.31.5"
    "And $FAC$, (which is) external to triangle $ABC$, is also equal to the two angles $ABC$ and $ACB$ [Prop.~1.32]."
    (step5 : ∠ f:a:c = ∠ a:b:c + ∠ a:c:b) := by sorry

  euclid_sentence "3.31.6"
    "Thus, angle $BAC$ (is) also equal to $FAC$."
    (step6 : ∠ b:a:c = ∠ f:a:c) := by sorry

  euclid_sentence "3.31.7"
    "Thus, (they are) each right-angles. [Def.~1.10]."
    (step7 : ∠ b:a:c = ∟ ∧ ∠ f:a:c = ∟) := by sorry

  euclid_sentence "3.31.8"
    "Thus, the angle $BAC$ in the semi-circle $BAC$ is a right-angle."
    (step8 : ∠ b:a:c = ∟) := by sorry

  -- @assumption ("the two angles $ABC$ and $BAC$ of triangle $ABC$ are less than two right-angles", ∠ a:b:c + ∠ b:a:c < ∟ + ∟)
  -- @assumption ("$BAC$ is a right-angle", ∠ b:a:c = ∟)
  euclid_sentence "3.31.9"
    "And since the two angles $ABC$ and $BAC$ of triangle $ABC$ are less than two right-angles [Prop.~1.17], and $BAC$ is a right-angle, angle $ABC$ is thus less than a right-angle."
    (step9 : ∠ a:b:c < ∟) := by sorry

  -- Locational: B is in the greater segment (apex B on opposite side of chord AC from D)
  euclid_sentence "3.31.10"
    "And it is in segment $ABC$, (which is) greater than a semi-circle."
    (step10 : ∠ a:b:c < ∟ ∧ b.opposingSides d AC) := by sorry

  -- @assumption ("$ABCD$ is a quadrilateral within a circle", a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD)
  -- @assumption ("the (sum of the) opposite angles is equal to two right-angles", ∠ a:b:c + ∠ a:d:c = ∟ + ∟)
  -- @assumption ("(angle) $ABC$ is less than a right-angle", ∠ a:b:c < ∟)
  euclid_sentence "3.31.11"
    "And since $ABCD$ is a quadrilateral within a circle, and for quadrilaterals within circles the (sum of the) opposite angles is equal to two right-angles [Prop.~3.22] [angles $ABC$ and $ADC$ are thus equal to two right-angles], and (angle) $ABC$ is less than a right-angle. The remaining angle $ADC$ is thus greater than a right-angle."
    (step11 : ∠ a:d:c > ∟) := by sorry

  -- Locational: D is in the lesser segment (apex D on opposite side of chord AC from B)
  euclid_sentence "3.31.12"
    "And it is in segment $ADC$, (which is) less than a semi-circle."
    (step12 : ∠ a:d:c > ∟ ∧ d.opposingSides b AC) := by sorry

  euclid_wts "3.31.13"
    "I also say that the angle of the greater segment, (namely) that contained by the circumference $ABC$ and the straight-line $AC$, is greater than a right-angle. And the angle of the lesser segment, (namely) that contained by the circumference $AD[C]$ and the straight-line $AC$, is less than a right-angle."

  -- orchestrator-HORN-unrenderable: "immediately apparent" refers to the horn angle comparison
  -- (curvilinear arc-and-chord angles vs. right-angle). System E has no curved-angle sort.
  -- Expressible basis: the established right-angles BAC and FAC that make the comparison immediate.
  euclid_sentence "3.31.14"
    "And this is immediately apparent."
    (step14 : ∠ b:a:c = ∟ ∧ ∠ f:a:c = ∟) := by sorry

  -- @assumption ("the (angle contained by) the two straight-lines $BA$ and $AC$ is a right-angle", ∠ b:a:c = ∟)
  -- orchestrator-HORN-unrenderable: the assertion "arc ABC ∧ line AC forms an angle greater than
  -- a right-angle" is a curvilinear (horn) angle — no System-E curved-angle sort. Expressible
  -- gloss (Reading A): chord AC cuts the circle at two distinct points a and c.
  euclid_sentence "3.31.15"
    "For since the (angle contained by) the two straight-lines $BA$ and $AC$ is a right-angle, the (angle) contained by the circumference $ABC$ and the straight-line $AC$ is thus greater than a right-angle."
    (step15 : AC.intersectsCircle ABCD) := by sorry

  -- @assumption ("the (angle contained by) the straight-lines $AC$ and $AF$ is a right-angle", ∠ f:a:c = ∟)
  -- orchestrator-HORN-unrenderable: the assertion "arc ADC ∧ line CA forms an angle less than
  -- a right-angle" is a curvilinear (horn) angle — no System-E curved-angle sort. Expressible
  -- gloss (Reading A): chord AC cuts the circle at two distinct points a and c.
  euclid_sentence "3.31.16"
    "Again, since the (angle contained by) the straight-lines $AC$ and $AF$ is a right-angle, the (angle) contained by the circumference $AD[C]$ and the straight-line $CA$ is thus less than a right-angle."
    (step16 : AC.intersectsCircle ABCD) := by sorry

  exact ⟨step8, step9, step11⟩
  euclid_conclude_sentence "3.31.17"
    "Thus, in a circle, the angle in a semi-circle is a right-angle, and that in a greater segment (is) less than a right-angle, and that in a lesser [segment] (is) greater than a right-angle. And, further, the [angle] of a segment greater (than a semi-circle) [is] greater than a right-angle, and the [angle] of a segment less (than a semi-circle) is less than a right-angle. (Which is) the very thing it was required to show."

end Elements.Book3
