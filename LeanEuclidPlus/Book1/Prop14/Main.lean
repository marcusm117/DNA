import SystemE
import Book1.Prop14.step1
import Book1.Prop14.step2
import Book1.Prop14.step3
import Book1.Prop14.step4
import Book1.Prop14.step5
import Book1.Prop14.step6
import Book1.Prop14.step7
import Book1.Prop14.step10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_14 : ∀ (a b c d : Point) (AB BC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ distinctPointsOnLine b d BD ∧ (c.opposingSides d AB) ∧
  (∠ a:b:c + ∠ a:b:d) = ∟ + ∟ →
  BC = BD := by
  euclid_intros
  euclid_intro_sentence "1.14.0"
    "If two straight-lines, not lying on the same side,  make adjacent angles (whose sum is) equal to two right-angles  with some straight-line, at a point on it, then the two straight-lines will be straight-on (with respect) to one another. For let two straight-lines $BC$ and $BD$, not lying on the same side,  make adjacent angles $ABC$ and $ABD$ (whose sum is) equal to two right-angles with some straight-line $AB$, at the point $B$ on it. I say that $BD$ is  straight-on with respect to $CB$. "
  -- Euclid argues by contradiction: suppose BD is not straight-on to CB (BC ≠ BD).
  have habsurd : ¬ (BC ≠ BD) := by
    intro hne
    euclid_apply (extend_point BC c b) as e
    -- @assumption_valid
    have step1_assumption1 : BD ≠ BC := by euclid_finish
    --@assumption ("if $BD$ is not straight-on to $BC$", BD ≠ BC)
    euclid_sentence "1.14.1"
      "For if $BD$ is not straight-on to $BC$ then let $BE$ be straight-on to $CB$. "
      (step1 : between c b e) := by euclid_apply (helper_1_14_step1 c b e BC BD (by euclid_assumption "" (show between c b e; assumption)) (by euclid_assumption "if $BD$ is not straight-on to $BC$" (show BD ≠ BC; assumption)))

    -- @assumption_valid
    have step2_assumption1 : between c b e := by assumption
    -- @assumption ("since the straight-line $AB$ stands on the straight-line $CBE$", between c b e)
    euclid_sentence "1.14.2"
      "Therefore, since the straight-line $AB$ stands on the straight-line $CBE$, the (sum of the) angles $ABC$ and $ABE$ is thus equal to two right-angles [Prop.~1.13]."
      (step2 : ∠ a:b:c + ∠ a:b:e = ∟ + ∟) := by euclid_apply (helper_1_14_step2 a b c e AB BC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "since the straight-line $AB$ stands on the straight-line $CBE$" (show between c b e; assumption)))

    euclid_sentence "1.14.3"
      "But (the sum of) $ABC$ and $ABD$ is also equal to two right-angles."
      (step3 : ∠ a:b:c + ∠ a:b:d = ∟ + ∟) := by euclid_apply (helper_1_14_step3 a b c d (by euclid_assumption "" (show ∠ a:b:c + ∠ a:b:d = ∟ + ∟; assumption)))

    euclid_sentence "1.14.4"
      "Thus,  (the sum of angles) $CBA$ and $ABE$ is equal to (the sum of angles) $CBA$ and $ABD$ [C.N.~1]."
      (step4 : ∠ c:b:a + ∠ a:b:e = ∠ c:b:a + ∠ a:b:d) := by euclid_apply (helper_1_14_step4 a b c d e (by euclid_assumption "" (show ∠ a:b:c + ∠ a:b:e = ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:c + ∠ a:b:d = ∟ + ∟; assumption)))

    euclid_sentence "1.14.5"
      "Let (angle) $CBA$ have been subtracted from both."
      (step5 : ∠ a:b:e = ∠ a:b:d) := by euclid_apply (helper_1_14_step5 a b c d e (by euclid_assumption "" (show ∠ c:b:a + ∠ a:b:e = ∠ c:b:a + ∠ a:b:d; assumption)))

    euclid_sentence "1.14.6"
      "Thus, the remainder $ABE$ is equal to the remainder $ABD$ [C.N.~3], the lesser to the greater."
      (step6 : ∠ a:b:e = ∠ a:b:d) := by euclid_apply (helper_1_14_step6 a b d e (by euclid_assumption "" (show ∠ a:b:e = ∠ a:b:d; assumption)))

    euclid_sentence "1.14.7"
      "The very thing is impossible."
      (step7 : False) := by euclid_apply (helper_1_14_step7 a b c d e AB BC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show ¬d.onLine AB; assumption)) (by euclid_assumption "" (show ¬c.sameSide d AB; assumption)) (by euclid_assumption "" (show BC ≠ BD; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between c b e; assumption)) (by euclid_assumption "" (show ∠ a:b:c + ∠ a:b:e = ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∠ a:b:d; assumption)))

    exact step7

  euclid_conclude_sentence "1.14.8"
    "Thus, $BE$ is not straight-on with respect to $CB$."
  euclid_conclude_sentence "1.14.9"
    "Similarly, we can show that neither (is) any other (straight-line)   than $BD$."
  euclid_sentence "1.14.10"
    "Thus, $CB$ is straight-on with respect to $BD$. "
    (step10 : BC = BD) := by euclid_apply (helper_1_14_step10 BC BD (by euclid_assumption "" (show ¬ BC ≠ BD; assumption)))

  exact step10
  euclid_conclude_sentence "1.14.11"
    "Thus, if two straight-lines, not lying on the same side,  make adjacent angles (whose sum is) equal to two right-angles with some straight-line, at a point on it, then the two straight-lines will be straight-on (with respect) to one another. (Which is) the very thing it was required to show."

end Elements.Book1
