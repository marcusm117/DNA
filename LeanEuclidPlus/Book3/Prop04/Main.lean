import SystemE
import Book3.Prop01.Main
import Book3.Prop04.step1
import Book3.Prop04.step2
import Book3.Prop04.step3
import Book3.Prop04.step4
import Book3.Prop04.step5
import Book3.Prop04.step6
import Book3.Prop04.step7
import Book3.Prop04.step8
import Book3.Prop04.step9
import Book3.Prop04.step10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_4 : ∀ (a b c d e f : Point) (AC BD : Line) (ABCD : Circle),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  f.isCentre ABCD ∧ ¬f.onLine AC ∧ ¬f.onLine BD ∧
  AC ≠ BD ∧ between a e c ∧ between b e d →
  ¬(|(a─e)| = |(e─c)| ∧ |(b─e)| = |(e─d)|) :=
by
  euclid_intros
  euclid_intro_sentence "3.4.0"
    "In a circle, if two straight-lines, which are not through the center, cut one another, (then) they do not cut one another in half. Let $ABCD$ be a circle, and within it, let two straight-lines, $AC$ and $BD$, which are not through the center, cut one another at (point) $E$. I say that they do not cut one another in half."

  euclid_sentence "3.4.1"
    "For, if possible, let them cut one another in half, such that $AE$ is equal to $EC$,"
    (step1 : |(a─e)| = |(e─c)|) := by euclid_apply (helper_3_4_step1 a e c (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)))

  euclid_sentence "3.4.2"
    "and $BE$ to $ED$."
    (step2 : |(b─e)| = |(e─d)|) := by euclid_apply (helper_3_4_step2 b e d (by euclid_assumption "" (show |(b─e)| = |(e─d)|; assumption)))

  -- note this is redundant, but faithful. Euclid is justifying how we construct the center, not that it exists, since existence is assumed.
  euclid_apply (proposition_1 ABCD) as f'
  euclid_sentence "3.4.3"
    "And let the center of the circle $ABCD$ be found [Prop.~3.1], and let it be (at point) $F$,"
    (step3 : f'.isCentre ABCD ∧ f' = f) := by euclid_apply (helper_3_4_step3 f' f ABCD (by euclid_assumption "" (show f'.isCentre ABCD; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)))

  euclid_apply (line_from_points f e) as FE
  euclid_sentence "3.4.4"
    "and let $FE$ be joined."
    (step4 : distinctPointsOnLine f e FE) := by euclid_apply (helper_3_4_step4 a c f e ABCD AC FE (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)))

  -- @assumption_valid
  have step5_assumption1 : |(a─e)| = |(e─c)| := by assumption
  -- @assumption ("some straight-line through the center, $FE$, cuts in half some straight-line not through the center, $AC$", |(a─e)| = |(e─c)|)
  euclid_sentence "3.4.5"
    "Therefore, since some straight-line through the center, $FE$, cuts in half some straight-line not through the center, $AC$, it also cuts it at right-angles [Prop.~3.3]."
    (step5 : ∠ f:e:a = ∟) := by euclid_apply (helper_3_4_step5 a c f e ABCD AC FE (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "some straight-line through the center, $FE$, cuts in half some straight-line not through the center, $AC$" (show |(a─e)| = |(e─c)|; assumption)))

  euclid_sentence "3.4.6"
    "Thus, $FEA$ is a right-angle."
    (step6 : ∠ f:e:a = ∟) := by euclid_apply (helper_3_4_step6 f e a (by euclid_assumption "" (show ∠ f:e:a = ∟; assumption)))

  -- @assumption_valid
  have step7_assumption1 : |(b─e)| = |(e─d)| := by assumption
  -- @assumption ("some straight-line $FE$ cuts in half some straight-line $BD$", |(b─e)| = |(e─d)|)
  euclid_sentence "3.4.7"
    "Again, since some straight-line $FE$ cuts in half some straight-line $BD$, it also cuts it at right-angles [Prop.~3.3]."
    (step7 : ∠ f:e:b = ∟) := by euclid_apply (helper_3_4_step7 b d f e ABCD BD FE (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show f.isCentre ABCD; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)) (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "some straight-line $FE$ cuts in half some straight-line $BD$" (show |(b─e)| = |(e─d)|; assumption)))

  euclid_sentence "3.4.8"
    "Thus, $FEB$ (is) a right-angle."
    (step8 : ∠ f:e:b = ∟) := by euclid_apply (helper_3_4_step8 f e b (by euclid_assumption "" (show ∠ f:e:b = ∟; assumption)))

  -- @assumption_valid
  have step9_assumption1 : ∠ f:e:a = ∟ := by assumption
  -- @assumption ("But $FEA$ was also shown (to be) a right-angle", ∠ f:e:a = ∟)
  euclid_sentence "3.4.9"
    "But $FEA$ was also shown (to be) a right-angle. Thus, $FEA$ (is) equal to $FEB$, the lesser to the greater."
    (step9 : ∠ f:e:a = ∠ f:e:b) := by euclid_apply (helper_3_4_step9 f e a b (by euclid_assumption "But $FEA$ was also shown (to be) a right-angle" (show ∠ f:e:a = ∟; assumption)) (by euclid_assumption "" (show ∠ f:e:b = ∟; assumption)))

  -- @euclid_gap: Euclid says "two straight-lines that cut one another" (implicitly AC≠BD).
  -- Without AC≠BD, the degenerate AC=BD case is a counterexample (same chord given twice,
  -- both bisected at e). Fixed by adding AC≠BD to the signature.
  euclid_sentence "3.4.10"
    "The very thing is impossible."
    (step10 : False) := by euclid_apply (helper_3_4_step10 a b c d e f AC BD FE ABCD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)) (by euclid_assumption "" (show distinctPointsOnLine f e FE; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between b e d; assumption)) (by euclid_assumption "" (show AC ≠ BD; assumption)) (by euclid_assumption "" (show ∠ f:e:a = ∟; assumption)) (by euclid_assumption "" (show ∠ f:e:b = ∟; assumption)))

  exact step10
  euclid_conclude_sentence "3.4.11"
    "Thus, $AC$ and $BD$ do not cut one another in half."
  euclid_conclude_sentence "3.4.12"
    "Thus, in a circle, if two straight-lines, which are not through the center, cut one another, (then) they do not cut one another in half. (Which is) the very thing it was required to show."

end Elements.Book3
