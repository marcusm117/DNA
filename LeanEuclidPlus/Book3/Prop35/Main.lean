import SystemE
import Book3.Prop01.Main
import Book1.Prop12.Main
import Book3.Prop35.step1
import Book3.Prop35.step2
import Book3.Prop35.step3
import Book3.Prop35.step4
import Book3.Prop35.step5
import Book3.Prop35.step6
import Book3.Prop35.step7
import Book3.Prop35.step8
import Book3.Prop35.step9
import Book3.Prop35.step10
import Book3.Prop35.step11
import Book3.Prop35.step12
import Book3.Prop35.step13
import Book3.Prop35.step14
import Book3.Prop35.step15
import Book3.Prop35.step16
import Book3.Prop35.step17
import Book3.Prop35.step18
import Book3.Prop35.step19
import Book3.Prop35.gapDiam
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem proposition_35 : ∀ (a b c d e : Point) (ABCD : Circle),
    a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
    between a e c ∧ between b e d →
    |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)| :=
by
  euclid_intros
  euclid_intro_sentence "3.35.0"
    "If two straight-lines in a circle cut one another, (then) the rectangle contained by the pieces of one is equal to the rectangle contained by the pieces of the other. For let the two straight-lines $AC$ and $BD$, in the circle $ABCD$, cut one another at point $E$. I say that the rectangle contained by $AE$ and $EC$ is equal to the rectangle contained by $DE$ and $EB$."

  by_cases hcen : e.isCentre ABCD
  ·
    -- @assumption_valid
    have step1_assumption1 : |(a─e)| = |(e─c)| ∧ |(e─c)| = |(d─e)| ∧ |(d─e)| = |(b─e)| := by euclid_finish
    -- @assumption ("$AE$, $EC$, $DE$, and $EB$ being equal", |(a─e)| = |(e─c)| ∧ |(e─c)| = |(d─e)| ∧ |(d─e)| = |(b─e)|)
    euclid_sentence "3.35.1"
      "In fact, if $AC$ and $BD$ are through the center (as in the first diagram from the left), so that $E$ is the center of circle $ABCD$, (then it is) clear that, $AE$, $EC$, $DE$, and $EB$ being equal, the rectangle contained by $AE$ and $EC$ is also equal to the rectangle contained by $DE$ and $EB$."
      (step1 : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)|) := by euclid_apply (helper_3_35_step1 a b c d e (by euclid_assumption "$AE$, $EC$, $DE$, and $EB$ being equal" (show |(a─e)| = |(e─c)| ∧ |(e─c)| = |(d─e)| ∧ |(d─e)| = |(b─e)|; assumption)))

    exact step1
  · euclid_apply (proposition_1 ABCD) as f
    euclid_sentence "3.35.2"
      "So let $AC$ and $DB$ not be though the center (as in the second diagram from the left), and let the center of $ABCD$ be found [Prop.~3.1], and let it be (at) $F$."
      (step2 : f.isCentre ABCD) := by euclid_apply (helper_3_35_step2 f ABCD (by euclid_assumption "" (show f.isCentre ABCD; assumption)))

    euclid_apply (line_from_points a c) as AC
    euclid_apply (line_from_points b d) as BD
    -- @euclid_gap: at least one of $AC$, $BD$ passes through the centre $F$ (i.e. is a diameter).
    --   Euclid's second diagram assumes NEITHER chord is through the centre; this configuration
    --   (admissible, since $E$ off-centre forces at most one chord to be a diameter) is omitted by
    --   Euclid. His theorem still holds; we prove it by the power of the point $E$.
    by_cases hdiam : f.onLine AC ∨ f.onLine BD
    ·
      have gapDiam : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)| := by euclid_apply (helper_3_35_gapDiam a b c d e f ABCD AC BD (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)))
      exact gapDiam
    have hf_off_AC : ¬f.onLine AC := fun h => hdiam (Or.inl h)
    have hf_off_BD : ¬f.onLine BD := fun h => hdiam (Or.inr h)
    euclid_apply (proposition_12 a c f AC) as g
    euclid_apply (proposition_12 b d f BD) as h
    euclid_sentence "3.35.3"
      "And let $FG$ and $FH$ be drawn from $F$, perpendicular to the straight-lines $AC$ and $DB$ (respectively) [Prop.~1.12]."
      (step3 : g.onLine AC ∧ (∠ a:g:f = ∟ ∨ ∠ c:g:f = ∟) ∧ h.onLine BD ∧ (∠ b:h:f = ∟ ∨ ∠ d:h:f = ∟)) := by euclid_apply (helper_3_35_step3 a b c d f g h AC BD (by euclid_assumption "" (show g.onLine AC; assumption)) (by euclid_assumption "" (show ∠ a:g:f = ∟ ∨ ∠ c:g:f = ∟; assumption)) (by euclid_assumption "" (show h.onLine BD; assumption)) (by euclid_assumption "" (show ∠ b:h:f = ∟ ∨ ∠ d:h:f = ∟; assumption)))

    euclid_apply (line_from_points f b) as FB
    euclid_apply (line_from_points f c) as FC
    euclid_apply (line_from_points f e) as FE
    euclid_sentence "3.35.4"
      "And let $FB$, $FC$, and $FE$ be joined."
      (step4 : distinctPointsOnLine f b FB ∧ distinctPointsOnLine f c FC ∧ distinctPointsOnLine f e FE) := by euclid_apply (helper_3_35_step4 b c e f ABCD FB FC FE (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show ¬e.isCentre ABCD; assumption)) (by euclid_assumption "" (show f.onLine FB; assumption)) (by euclid_assumption "" (show b.onLine FB; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)))

    -- @assumption_valid
    have step5_assumption1 : (∠ a:g:f = ∟ ∨ ∠ c:g:f = ∟) ∧ ¬f.onLine AC := by euclid_finish
    -- @assumption ("some straight-line, $GF$, through the center, cuts at right-angles some (other) straight-line, $AC$, not through the center", (∠ a:g:f = ∟ ∨ ∠ c:g:f = ∟) ∧ ¬f.onLine AC)
    euclid_sentence "3.35.5"
      "And since some straight-line, $GF$, through the center, cuts at right-angles some (other) straight-line, $AC$, not through the center, (then) it also cuts it in half [Prop.~3.3]."
      (step5 : |(a─g)| = |(g─c)|) := by euclid_apply (helper_3_35_step5 a c e f g ABCD AC (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine AC; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine AC → p ≠ g → ∠ p:g:f = ∟; assumption)) (by euclid_assumption "some straight-line, $GF$, through the center, cuts at right-angles some (other) straight-line, $AC$, not through the center" (show (∠ a:g:f = ∟ ∨ ∠ c:g:f = ∟) ∧ ¬f.onLine AC; assumption)))

    euclid_sentence "3.35.6"
      "Thus, $AG$ (is) equal to $GC$."
      (step6 : |(a─g)| = |(g─c)|) := by euclid_apply (helper_3_35_step6 a c g (by euclid_assumption "" (show |(a─g)| = |(g─c)|; assumption)))

    -- @assumption_valid
    have step7_assumption1 : |(a─g)| = |(g─c)| := by assumption
    -- @assumption ("the straight-line $AC$ is cut equally at $G$, and unequally at $E$", |(a─g)| = |(g─c)|)
    euclid_sentence "3.35.7"
      "Therefore, since the straight-line $AC$ is cut equally at $G$, and unequally at $E$, the rectangle contained by $AE$ and $EC$ plus the square on $EG$ is thus equal to the (square) on $GC$ [Prop.~2.5]."
      (step7 : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| = |(g─c)| * |(g─c)|) := by euclid_apply (helper_3_35_step7 a c e g AC (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine AC; assumption)) (by euclid_assumption "the straight-line $AC$ is cut equally at $G$, and unequally at $E$" (show |(a─g)| = |(g─c)|; assumption)))

    euclid_sentence "3.35.8"
      "Let the (square) on $GF$ be added [to both]."
      (step8 : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = |(g─c)| * |(g─c)| + |(g─f)| * |(g─f)|) := by euclid_apply (helper_3_35_step8 a c e g f (by euclid_assumption "" (show |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| = |(g─c)| * |(g─c)|; assumption)))

    euclid_sentence "3.35.9"
      "Thus, the (rectangle contained) by $AE$ and $EC$ plus the (sum of the squares) on $GE$ and $GF$ is equal to the (sum of the squares) on $CG$ and $GF$."
      (step9 : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = |(g─c)| * |(g─c)| + |(g─f)| * |(g─f)|) := by euclid_apply (helper_3_35_step9 a c e g f (by euclid_assumption "" (show |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = |(g─c)| * |(g─c)| + |(g─f)| * |(g─f)|; assumption)))

    euclid_sentence "3.35.10"
      "But, the (square) on $FE$ is equal to the (sum of the squares) on $EG$ and $GF$ [Prop.~1.47],"
      (step10 : |(f─e)| * |(f─e)| = |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)|) := by euclid_apply (helper_3_35_step10 a c e f g AC FE (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine AC; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine AC → p ≠ g → ∠ p:g:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)))

    euclid_sentence "3.35.11"
      "and the (square) on $FC$ is equal to the (sum of the squares) on $CG$ and $GF$ [Prop.~1.47]."
      (step11 : |(f─c)| * |(f─c)| = |(c─g)| * |(c─g)| + |(g─f)| * |(g─f)|) := by euclid_apply (helper_3_35_step11 c f g AC FC (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine AC; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine AC → p ≠ g → ∠ p:g:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)))

    euclid_sentence "3.35.12"
      "Thus, the (rectangle contained) by $AE$ and $EC$ plus the (square) on $FE$ is equal to the (square) on $FC$."
      (step12 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─c)| * |(f─c)|) := by euclid_apply (helper_3_35_step12 a c e f g (by euclid_assumption "" (show |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| = |(g─c)| * |(g─c)|; assumption)) (by euclid_assumption "" (show |(f─e)| * |(f─e)| = |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)|; assumption)) (by euclid_assumption "" (show |(f─c)| * |(f─c)| = |(c─g)| * |(c─g)| + |(g─f)| * |(g─f)|; assumption)))

    euclid_sentence "3.35.13"
      "And $FC$ (is) equal to $FB$."
      (step13 : |(f─c)| = |(f─b)|) := by euclid_apply (helper_3_35_step13 b c f ABCD (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)))

    euclid_sentence "3.35.14"
      "Thus, the (rectangle contained) by $AE$ and $EC$ plus the (square) on $FE$ is equal to the (square) on $FB$."
      (step14 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|) := by euclid_apply (helper_3_35_step14 a b c e f (by euclid_assumption "" (show |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─c)| * |(f─c)|; assumption)) (by euclid_assumption "" (show |(f─c)| = |(f─b)|; assumption)))

    euclid_sentence "3.35.15"
      "So, for the same (reasons), the (rectangle contained) by $DE$ and $EB$ plus the (square) on $FE$ is equal to the (square) on $FB$."
      (step15 : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|) := by euclid_apply (helper_3_35_step15 b d e f ABCD BD (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)))

    euclid_sentence "3.35.16"
      "And the (rectangle contained) by $AE$ and $EC$ plus the (square) on $FE$ was also shown (to be) equal to the (square) on $FB$."
      (step16 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|) := by euclid_apply (helper_3_35_step16 a b c e f (by euclid_assumption "" (show |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|; assumption)))

    euclid_sentence "3.35.17"
      "Thus, the (rectangle contained) by $AE$ and $EC$ plus the (square) on $FE$ is equal to the (rectangle contained) by $DE$ and $EB$ plus the (square) on $FE$."
      (step17 : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)|) := by euclid_apply (helper_3_35_step17 a b c d e f (by euclid_assumption "" (show |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|; assumption)) (by euclid_assumption "" (show |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)|; assumption)))

    euclid_sentence "3.35.18"
      "Let the (square) on $FE$ be taken from both."
      (step18 : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)|) := by euclid_apply (helper_3_35_step18 a b c d e f (by euclid_assumption "" (show |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)|; assumption)))

    euclid_sentence "3.35.19"
      "Thus, the remaining rectangle contained by $AE$ and $EC$ is equal to the rectangle contained by $DE$ and $EB$."
      (step19 : |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)|) := by euclid_apply (helper_3_35_step19 a b c d e (by euclid_assumption "" (show |(a─e)| * |(e─c)| = |(b─e)| * |(e─d)|; assumption)))

    exact step19
    euclid_conclude_sentence "3.35.20"
      "Thus, if two straight-lines in a circle cut one another, (then) the rectangle contained by the pieces of one is equal to the rectangle contained by the pieces of the other. (Which is) the very thing it was required to show."

end Elements.Book3
