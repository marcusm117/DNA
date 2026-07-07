import SystemE
import Book3.Prop01.Main
import Book1.Prop12.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_35 : ∀ (a b c d e : Point) (ABCD : Circle),
    a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
    between a e c ∧ between b e d →
    |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)| :=
by
  euclid_intros
  euclid_intro_sentence "3.35.0"
    "If two straight-lines in a circle cut one another, (then) the rectangle contained by the pieces of one is equal to the rectangle contained by the pieces of the other. For let the two straight-lines $AC$ and $BD$, in the circle $ABCD$, cut one another at point $E$. I say that the rectangle contained by $AE$ and $EC$ is equal to the rectangle contained by $DE$ and $EB$."

  -- @assumption ("$AC$ and $BD$ are through the center (as in the first diagram from the left), so that $E$ is the center of circle $ABCD$", e.isCentre ABCD)
  -- @assumption ("$AE$, $EC$, $DE$, and $EB$ being equal", |(a─e)| = |(e─c)| ∧ |(e─c)| = |(d─e)| ∧ |(d─e)| = |(b─e)|)
  euclid_sentence "3.35.1"
    "In fact, if $AC$ and $BD$ are through the center (as in the first diagram from the left), so that $E$ is the center of circle $ABCD$, (then it is) clear that, $AE$, $EC$, $DE$, and $EB$ being equal, the rectangle contained by $AE$ and $EC$ is also equal to the rectangle contained by $DE$ and $EB$."
    (step1 : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)|) := by sorry

  euclid_apply (proposition_1 ABCD) as f
  -- @assumption ("$AC$ and $DB$ not be though the center", ¬e.isCentre ABCD)
  euclid_sentence "3.35.2"
    "So let $AC$ and $DB$ not be though the center (as in the second diagram from the left), and let the center of $ABCD$ be found [Prop.~3.1], and let it be (at) $F$."
    (step2 : f.isCentre ABCD) := by sorry

  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points b d) as BD
  have hf_off_AC : ¬f.onLine AC := by sorry
  have hf_off_BD : ¬f.onLine BD := by sorry
  euclid_apply (proposition_12 a c f AC) as g
  euclid_apply (proposition_12 b d f BD) as h
  euclid_sentence "3.35.3"
    "And let $FG$ and $FH$ be drawn from $F$, perpendicular to the straight-lines $AC$ and $DB$ (respectively) [Prop.~1.12]."
    (step3 : g.onLine AC ∧ (∠ a:g:f = ∟ ∨ ∠ c:g:f = ∟) ∧ h.onLine BD ∧ (∠ b:h:f = ∟ ∨ ∠ d:h:f = ∟)) := by sorry

  euclid_apply (line_from_points f b) as FB
  euclid_apply (line_from_points f c) as FC
  euclid_apply (line_from_points f e) as FE
  euclid_sentence "3.35.4"
    "And let $FB$, $FC$, and $FE$ be joined."
    (step4 : distinctPointsOnLine f b FB ∧ distinctPointsOnLine f c FC ∧ distinctPointsOnLine f e FE) := by sorry

  -- @assumption ("some straight-line, $GF$, through the center, cuts at right-angles some (other) straight-line, $AC$, not through the center", (∠ a:g:f = ∟ ∨ ∠ c:g:f = ∟) ∧ ¬f.onLine AC)
  euclid_sentence "3.35.5"
    "And since some straight-line, $GF$, through the center, cuts at right-angles some (other) straight-line, $AC$, not through the center, (then) it also cuts it in half [Prop.~3.3]."
    (step5 : |(a─g)| = |(g─c)|) := by sorry

  euclid_sentence "3.35.6"
    "Thus, $AG$ (is) equal to $GC$."
    (step6 : |(a─g)| = |(g─c)|) := by sorry

  -- @assumption ("the straight-line $AC$ is cut equally at $G$, and unequally at $E$", |(a─g)| = |(g─c)| ∧ between a g e ∧ between g e c)
  euclid_sentence "3.35.7"
    "Therefore, since the straight-line $AC$ is cut equally at $G$, and unequally at $E$, the rectangle contained by $AE$ and $EC$ plus the square on $EG$ is thus equal to the (square) on $GC$ [Prop.~2.5]."
    (step7 : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| = |(g─c)| * |(g─c)|) := by sorry

  euclid_sentence "3.35.8"
    "Let the (square) on $GF$ be added [to both]."
    (step8 : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = |(g─c)| * |(g─c)| + |(g─f)| * |(g─f)|) := by sorry

  euclid_sentence "3.35.9"
    "Thus, the (rectangle contained) by $AE$ and $EC$ plus the (sum of the squares) on $GE$ and $GF$ is equal to the (sum of the squares) on $CG$ and $GF$."
    (step9 : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = |(g─c)| * |(g─c)| + |(g─f)| * |(g─f)|) := by sorry

  euclid_sentence "3.35.10"
    "But, the (square) on $FE$ is equal to the (sum of the squares) on $EG$ and $GF$ [Prop.~1.47],"
    (step10 : |(f─e)| * |(f─e)| = |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)|) := by sorry

  euclid_sentence "3.35.11"
    "and the (square) on $FC$ is equal to the (sum of the squares) on $CG$ and $GF$ [Prop.~1.47]."
    (step11 : |(f─c)| * |(f─c)| = |(c─g)| * |(c─g)| + |(g─f)| * |(g─f)|) := by sorry

  euclid_sentence "3.35.12"
    "Thus, the (rectangle contained) by $AE$ and $EC$ plus the (square) on $FE$ is equal to the (square) on $FC$."
    (step12 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─c)| * |(f─c)|) := by sorry

  euclid_sentence "3.35.13"
    "And $FC$ (is) equal to $FB$."
    (step13 : |(f─c)| = |(f─b)|) := by sorry

  euclid_sentence "3.35.14"
    "Thus, the (rectangle contained) by $AE$ and $EC$ plus the (square) on $FE$ is equal to the (square) on $FB$."
    (step14 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|) := by sorry

  euclid_sentence "3.35.15"
    "So, for the same (reasons), the (rectangle contained) by $DE$ and $EB$ plus the (square) on $FE$ is equal to the (square) on $FB$."
    (step15 : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|) := by sorry

  euclid_sentence "3.35.16"
    "And the (rectangle contained) by $AE$ and $EC$ plus the (square) on $FE$ was also shown (to be) equal to the (square) on $FB$."
    (step16 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|) := by sorry

  euclid_sentence "3.35.17"
    "Thus, the (rectangle contained) by $AE$ and $EC$ plus the (square) on $FE$ is equal to the (rectangle contained) by $DE$ and $EB$ plus the (square) on $FE$."
    (step17 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)|) := by sorry

  euclid_sentence "3.35.18"
    "Let the (square) on $FE$ be taken from both."
    (step18 : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)|) := by sorry

  euclid_sentence "3.35.19"
    "Thus, the remaining rectangle contained by $AE$ and $EC$ is equal to the rectangle contained by $DE$ and $EB$."
    (step19 : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)|) := by sorry

  exact step19
  euclid_conclude_sentence "3.35.20"
    "Thus, if two straight-lines in a circle cut one another, (then) the rectangle contained by the pieces of one is equal to the rectangle contained by the pieces of the other. (Which is) the very thing it was required to show."

end Elements.Book3
