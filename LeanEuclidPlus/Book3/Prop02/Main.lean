import SystemE
import Book3.Prop01.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_2 : ∀ (a b : Point) (ABC : Circle),
  a.onCircle ABC ∧ b.onCircle ABC ∧ a ≠ b →
  ∀ p : Point, between a p b → p.insideCircle ABC :=
by
  euclid_intros
  euclid_intro_sentence "3.2.0"
    "If two points are taken at random on the circumference of a circle, (then) the straight-line joining the points will fall inside the circle. Let $ABC$ be a circle, and let two points $A$ and $B$ be taken at random on its circumference. I say that the straight-line joining $A$ to $B$ will fall inside the circle."

  have habsurd1 : ¬(p.outsideCircle ABC) := by
    intro hsuppose1
    euclid_sentence "3.2.1"
      "For (if) not (then), if possible, let it fall outside (the circle), like $AEB$ (in the figure)."
      (step1 : p.outsideCircle ABC) := by sorry

    euclid_apply (proposition_1 ABC) as d
    euclid_sentence "3.2.2"
      "And let the center of the circle $ABC$ be found [Prop.~3.1], and let it be (at point) $D$."
      (step2 : d.isCentre ABC) := by sorry

    euclid_apply (line_from_points d a) as DA
    euclid_apply (line_from_points d b) as DB
    euclid_sentence "3.2.3"
      "And let $DA$ and $DB$ be joined,"
      (step3 : distinctPointsOnLine d a DA ∧ distinctPointsOnLine d b DB) := by sorry

    euclid_apply (line_from_points d p) as DFE
    euclid_apply (intersection_circle_line_between_points ABC DFE d p) as f
    euclid_sentence "3.2.4"
      "and let $DFE$ be drawn through."
      (step4 : f.onCircle ABC ∧ between d f p) := by sorry

    -- @assumption ("$DA$ is equal to $DB$", |(d─a)| = |(d─b)|)
    euclid_sentence "3.2.5"
      "Therefore, since $DA$ is equal to $DB$, the angle $DAE$ (is) thus also equal to $DBE$ [Prop.~1.5]."
      (step5 : ∠ d:a:p = ∠ d:b:p) := by sorry

    -- @assumption ("in triangle $DAE$ the one side, $AEB$, has been produced", between a p b)
    euclid_sentence "3.2.6"
      "And since in triangle $DAE$ the one side, $AEB$, has been produced, angle $DEB$ (is) thus greater than $DAE$ [Prop.~1.16]."
      (step6 : ∠ d:p:b > ∠ d:a:p) := by sorry

    euclid_sentence "3.2.7"
      "And $DAE$ (is) equal to $DBE$ [Prop.~1.5]."
      (step7 : ∠ d:a:p = ∠ d:b:p) := by sorry

    euclid_sentence "3.2.8"
      "Thus, $DEB$ (is) greater than $DBE$."
      (step8 : ∠ d:p:b > ∠ d:b:p) := by sorry

    -- @assumption ("the greater angle is subtended by the greater side", ∠ d:p:b > ∠ d:b:p)
    euclid_sentence "3.2.9"
      "And the greater angle is subtended by the greater side [Prop.~1.19]. Thus, $DB$ (is) greater than $DE$."
      (step9 : |(d─b)| > |(d─p)|) := by sorry

    euclid_sentence "3.2.10"
      "And $DB$ (is) equal to $DF$."
      (step10 : |(d─b)| = |(d─f)|) := by sorry

    euclid_sentence "3.2.11"
      "Thus, $DF$ (is) greater than $DE$, the lesser than the greater."
      (step11 : |(d─f)| > |(d─p)|) := by sorry

    euclid_sentence "3.2.12"
      "The very thing is impossible."
      (step12 : False) := by sorry
    exact step12

  euclid_sentence "3.2.13"
    "Thus, the straight-line joining $A$ to $B$ will not fall outside the circle."
    (step13 : ¬(p.outsideCircle ABC)) := by sorry

  euclid_sentence "3.2.14"
    "So, similarly, we can show that neither (will it fall) on the circumference itself."
    (step14 : ¬(p.onCircle ABC)) := by sorry

  euclid_sentence "3.2.15"
    "Thus, (it will fall) inside (the circle)."
    (step15 : p.insideCircle ABC) := by sorry

  exact step15
  euclid_conclude_sentence "3.2.16"
    "Thus, if two points are taken at random on the circumference of a circle, (then) the straight-line joining the points will fall inside the circle. (Which is) the very thing it was required to show."

end Elements.Book3
