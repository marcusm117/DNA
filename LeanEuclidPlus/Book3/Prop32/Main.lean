import SystemE
import Book1.Prop11.Main
import Book3.Prop19.Main
import Book3.Prop32.step1
import Book3.Prop32.step2
import Book3.Prop32.step3
import Book3.Prop32.step4
import Book3.Prop32.step5
import Book3.Prop32.step6
import Book3.Prop32.step7
import Book3.Prop32.step8
import Book3.Prop32.step9
import Book3.Prop32.step10
import Book3.Prop32.step11
import Book3.Prop32.step12
import Book3.Prop32.step13
import Book3.Prop32.step14
import Book3.Prop32.step15
import Book3.Prop32.step_deg
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

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

  -- Euclid's point $A$ plays two roles that coincide in his single figure: (i) the endpoint of the
  -- perpendicular from $B$ (the antipode of $B$), and (ii) a point of segment $BAD$. Our theorem's `a`
  -- is the GENERIC point of segment $BAD$ (role ii); Euclid's perpendicular endpoint (role i) is the
  -- distinct point `a'`. Steps 3.32.1–3.32.10 are Euclid's argument about `a'`; step 3.32.11
  -- (`in the alternate segment`) carries the result to the generic `a` via [Prop.~3.21].
  euclid_apply (Elements.Book1.proposition_11 e f b EF) as p
  euclid_apply (line_from_points b p) as BA
  euclid_apply (exists_centre ABCD) as o
  euclid_apply (Elements.Book3.proposition_19 p b f ABCD EF BA)
  euclid_apply (intersection_circle_line_extending_points ABCD BA o b) as a'
  -- Euclid's figure assumes $D \ne A$ (chord $BD$ is not the diameter $BA$) — a generic-position gloss.
  -- When $D = A'$ ($BD$ IS a diameter) all four angles are right angles (angle in a semi-circle).
  by_cases hdeg : d = a'
  · have step_deg : ∠ f:b:d = ∠ b:a:d ∧ ∠ e:b:d = ∠ d:c:b := by euclid_apply (helper_3_32_step_deg b a d c e f p a' o ABCD EF BA BD (by euclid_assumption "" (show d = a'; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show ¬EF.intersectsCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onLine BA; assumption)) (by euclid_assumption "" (show p.onLine BA; assumption)) (by euclid_assumption "" (show a'.onLine BA; assumption)) (by euclid_assumption "" (show ∠ e:b:p = ∟; assumption)) (by euclid_assumption "" (show ¬p.onLine EF; assumption)) (by euclid_assumption "" (show o.isCentre ABCD; assumption)) (by euclid_assumption "" (show between a' o b; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)))
    exact step_deg
  · euclid_sentence "3.32.1"
      "For let $BA$ be drawn from $B$, at right-angles to $EF$ [Prop.~1.11]."
      (step1 : distinctPointsOnLine b a' BA ∧ ∠ a':b:f = ∟) := by euclid_apply (helper_3_32_step1 b a' p e f o ABCD EF BA (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show b.onLine BA; assumption)) (by euclid_assumption "" (show p.onLine BA; assumption)) (by euclid_assumption "" (show a'.onLine BA; assumption)) (by euclid_assumption "" (show ∠ e:b:p = ∟; assumption)) (by euclid_assumption "" (show ¬p.onLine EF; assumption)) (by euclid_assumption "" (show o.isCentre ABCD; assumption)) (by euclid_assumption "" (show between a' o b; assumption)))

    euclid_sentence "3.32.2"
      "And let the point $C$ be taken at random on the circumference $BD$."
      (step2 : c.onCircle ABCD) := by euclid_apply (helper_3_32_step2 c ABCD (by euclid_assumption "" (show c.onCircle ABCD; assumption)))

    euclid_apply (line_from_points a' d) as AD
    euclid_apply (line_from_points d c) as DC
    euclid_apply (line_from_points c b) as CB
    euclid_sentence "3.32.3"
      "And let $AD$, $DC$, and $CB$ be joined."
      (step3 : distinctPointsOnLine a' d AD ∧ distinctPointsOnLine d c DC ∧ distinctPointsOnLine c b CB) := by euclid_apply (helper_3_32_step3 a' d c b AD DC CB BD (by euclid_assumption "" (show a'.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d ≠ a'; assumption)))

    -- @assumption_valid
    have step4_assumption1 : b.onLine EF ∧ b.onCircle ABCD ∧ ¬EF.intersectsCircle ABCD := by euclid_finish
    -- @assumption_valid
    have step4_assumption2 : distinctPointsOnLine b a' BA ∧ ∠ a':b:f = ∟ := by euclid_finish
    -- @assumption ("some straight-line $EF$ touches the circle $ABCD$ at point $B$", b.onLine EF ∧ b.onCircle ABCD ∧ ¬EF.intersectsCircle ABCD)
    -- @assumption ("$BA$ has been drawn from the point of contact, at right-angles to the tangent", distinctPointsOnLine b a' BA ∧ ∠ a':b:f = ∟)
    euclid_sentence "3.32.4"
      "And since some straight-line $EF$ touches the circle $ABCD$ at point $B$, and $BA$ has been drawn from the point of contact, at right-angles to the tangent, the center of circle $ABCD$ is thus on $BA$ [Prop.~3.19]."
      (step4 : ∀ o : Point, o.isCentre ABCD → o.onLine BA) := by euclid_apply (helper_3_32_step4 b a' f e ABCD EF BA (by euclid_assumption "some straight-line $EF$ touches the circle $ABCD$ at point $B$" (show b.onLine EF ∧ b.onCircle ABCD ∧ ¬EF.intersectsCircle ABCD; assumption)) (by euclid_assumption "$BA$ has been drawn from the point of contact, at right-angles to the tangent" (show distinctPointsOnLine b a' BA ∧ ∠ a':b:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)))

    euclid_sentence "3.32.5"
      "Thus, $BA$ is a diameter of circle $ABCD$."
      (step5 : ∃ o : Point, o.isCentre ABCD ∧ between a' o b ∧ a'.onCircle ABCD ∧ b.onCircle ABCD) := by euclid_apply (helper_3_32_step5 a' b ABCD BA (by euclid_assumption "" (show a'.onLine BA; assumption)) (by euclid_assumption "" (show b.onLine BA; assumption)) (by euclid_assumption "" (show b ≠ a'; assumption)) (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show ∀ o : Point, o.isCentre ABCD → o.onLine BA; assumption)))

    -- @suppress_deps_check "III.31 is skipped (its horn-angle segment addendum is not formalizable in System E); the semicircle right angle is re-derived in step6 from I.5 + I.32."
    euclid_sentence "3.32.6"
      "Thus, angle $ADB$, being in a semi-circle, is a right-angle [Prop.~3.31]."
      (step6 : ∠ a':d:b = ∟) := by euclid_apply (helper_3_32_step6 a' b d ABCD BA BD AD (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show a'.onLine BA; assumption)) (by euclid_assumption "" (show b.onLine BA; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show d ≠ a'; assumption)) (by euclid_assumption "" (show a'.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∃ o : Point, o.isCentre ABCD ∧ between a' o b ∧ a'.onCircle ABCD ∧ b.onCircle ABCD; assumption)))

    euclid_sentence "3.32.7"
      "Thus, the remaining angles (of triangle $ADB$) $BAD$ and $ABD$ are equal to one right-angle [Prop.~1.32]."
      (step7 : ∠ b:a':d + ∠ a':b:d = ∟) := by euclid_apply (helper_3_32_step7 a' b d ABCD BA BD AD (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show a'.onLine BA; assumption)) (by euclid_assumption "" (show b.onLine BA; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show d ≠ a'; assumption)) (by euclid_assumption "" (show a'.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ a':d:b = ∟; assumption)))

    euclid_sentence "3.32.8"
      "And $ABF$ is also a right-angle."
      (step8 : ∠ a':b:f = ∟) := by euclid_apply (helper_3_32_step8 a' b f (by euclid_assumption "" (show ∠ a':b:f = ∟; assumption)))

    euclid_sentence "3.32.9"
      "Thus, $ABF$ is equal to $BAD$ and $ABD$."
      (step9 : ∠ a':b:f = ∠ b:a':d + ∠ a':b:d) := by euclid_apply (helper_3_32_step9 a' b d f (by euclid_assumption "" (show ∠ b:a':d + ∠ a':b:d = ∟; assumption)) (by euclid_assumption "" (show ∠ a':b:f = ∟; assumption)))

    euclid_sentence "3.32.10"
      "Let $ABD$ be subtracted from both."
      (step10 : ∠ a':b:f - ∠ a':b:d = ∠ b:a':d) := by euclid_apply (helper_3_32_step10 a' b d f (by euclid_assumption "" (show ∠ a':b:f = ∠ b:a':d + ∠ a':b:d; assumption)))

    euclid_sentence "3.32.11"
      "Thus, the remaining angle $DBF$ is equal to the angle $BAD$ in the alternate segment of the circle."
      (step11 : ∠ f:b:d = ∠ b:a:d) := by euclid_apply (helper_3_32_step11 a a' b c d e f ABCD BD BA EF (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬e.onLine BD; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.sameSide f BD; assumption)) (by euclid_assumption "" (show ¬c.sameSide e BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show b ≠ a'; assumption)) (by euclid_assumption "" (show d ≠ a'; assumption)) (by euclid_assumption "" (show a'.onLine BA; assumption)) (by euclid_assumption "" (show b.onLine BA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show ∠ a':b:f = ∟; assumption)) (by euclid_assumption "" (show ¬EF.intersectsCircle ABCD; assumption)) (by euclid_assumption "" (show ∠ a':b:f = ∠ b:a':d + ∠ a':b:d; assumption)))

    -- @assumption_valid
    have step12_assumption1 : a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD := by euclid_finish
    -- @assumption ("$ABCD$ is a quadrilateral in a circle", a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD)
    euclid_sentence "3.32.12"
      "And since $ABCD$ is a quadrilateral in a circle, (the sum of) its opposite angles is equal to two right-angles [Prop.~3.22]."
      (step12 : ∠ b:a:d + ∠ b:c:d = ∟ + ∟) := by euclid_apply (helper_3_32_step12 a b c d e f ABCD BD EF (by euclid_assumption "$ABCD$ is a quadrilateral in a circle" (show a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬e.onLine BD; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.sameSide f BD; assumption)) (by euclid_assumption "" (show ¬c.sameSide e BD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)))

    euclid_sentence "3.32.13"
      "And $DBF$ and $DBE$ is also equal to two right-angles [Prop.~1.13]."
      (step13 : ∠ f:b:d + ∠ e:b:d = ∟ + ∟) := by euclid_apply (helper_3_32_step13 b d e f BD EF (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)))

    -- @assumption_valid
    have step14_assumption1 : ∠ f:b:d = ∠ b:a:d := by assumption
    -- @assumption ("$BAD$ was shown (to be) equal to $DBF$", ∠ f:b:d = ∠ b:a:d)
    euclid_sentence "3.32.14"
      "Thus, $DBF$ and $DBE$ is equal to $BAD$ and $BCD$, of which $BAD$ was shown (to be) equal to $DBF$."
      (step14 : ∠ f:b:d + ∠ e:b:d = ∠ b:a:d + ∠ b:c:d) := by euclid_apply (helper_3_32_step14 a b c d e f (by euclid_assumption "$BAD$ was shown (to be) equal to $DBF$" (show ∠ f:b:d = ∠ b:a:d; assumption)) (by euclid_assumption "" (show ∠ b:a:d + ∠ b:c:d = ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ f:b:d + ∠ e:b:d = ∟ + ∟; assumption)))

    euclid_sentence "3.32.15"
      "Thus, the remaining (angle) $DBE$ is equal to the angle $DCB$ in the alternate segment $DCB$ of the circle."
      (step15 : ∠ e:b:d = ∠ d:c:b) := by euclid_apply (helper_3_32_step15 a b c d e f BD (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ∠ f:b:d = ∠ b:a:d; assumption)) (by euclid_assumption "" (show ∠ f:b:d + ∠ e:b:d = ∠ b:a:d + ∠ b:c:d; assumption)))

    exact ⟨step11, step15⟩
    euclid_conclude_sentence "3.32.16"
      "Thus, if some straight-line touches a circle, and some (other) straight-line is drawn across, from the point of contact into the circle, cutting the circle (in two), (then) those angles the (straight-line) makes with the tangent will be equal to the angles in the alternate segments of the circle. (Which is) the very thing it was required to show."

end Elements.Book3
