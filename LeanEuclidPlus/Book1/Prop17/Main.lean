import SystemE
import Book1.Prop17.step1
import Book1.Prop17.step2
import Book1.Prop17.step3
import Book1.Prop17.step4
import Book1.Prop17.step5
import Book1.Prop17.step6
import Book1.Prop17.step7
import Book1.Prop17.step8
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_17 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC →
  ∠ a:b:c + ∠ b:c:a < ∟ + ∟ := by
  euclid_intros
  euclid_intro_sentence "1.17.0"
    "For any triangle,  (the sum of) two angles taken together in any (possible way) is less than two right-angles. Let $ABC$ be a triangle. I say that (the sum of) two angles of triangle $ABC$ taken together in any (possible way) is less than two right-angles. "

  euclid_apply (extend_point BC b c) as d
  euclid_sentence "1.17.1"
    "For let $BC$ have been produced to $D$. "
    (step1 : between b c d) := by euclid_apply (helper_1_17_step1 b c d (by euclid_assumption "" (show between b c d; assumption)))

  -- @assumption_valid
  have step2_assumption1 : between b c d := by assumption
  -- @assumption ("the angle $ACD$ is external to triangle $ABC$", between b c d)
  euclid_sentence "1.17.2"
    "And since the angle $ACD$ is external to triangle $ABC$, it is greater than the internal and opposite angle $ABC$ [Prop.~1.16]."
    (step2 : ∠ a:c:d > ∠ a:b:c) := by euclid_apply (helper_1_17_step2 a b c d AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "the angle $ACD$ is external to triangle $ABC$" (show between b c d; assumption)))

  euclid_sentence "1.17.3"
    "Let $ACB$ have been added to both."
    (step3 : ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ a:c:b) := by euclid_apply (helper_1_17_step3 a b c d (by euclid_assumption "" (show ∠ a:c:d > ∠ a:b:c; assumption)))

  euclid_sentence "1.17.4"
    "Thus, the (sum of the angles) $ACD$ and $ACB$ is greater than the  (sum of the angles) $ABC$ and $BCA$."
    (step4 : ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ b:c:a) := by euclid_apply (helper_1_17_step4 a b c d AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ a:c:b; assumption)))

  euclid_sentence "1.17.5"
    "But, (the sum of) $ACD$ and $ACB$ is equal to two right-angles [Prop.~1.13]."
    (step5 : ∠ a:c:d + ∠ a:c:b = ∟ + ∟) := by euclid_apply (helper_1_17_step5 a b c d AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show between b c d; assumption)))

  euclid_sentence "1.17.6"
    "Thus, (the sum of) $ABC$ and $BCA$ is less than two right-angles."
    (step6 : ∠ a:b:c + ∠ b:c:a < ∟ + ∟) := by euclid_apply (helper_1_17_step6 a b c d (by euclid_assumption "" (show ∠ a:c:d + ∠ a:c:b > ∠ a:b:c + ∠ b:c:a; assumption)) (by euclid_assumption "" (show ∠ a:c:d + ∠ a:c:b = ∟ + ∟; assumption)))

  euclid_sentence "1.17.7"
    "Similarly, we can show that (the sum of) $BAC$ and $ACB$ is also less than two right-angles,"
    (step7 : ∠ b:a:c + ∠ a:c:b < ∟ + ∟) := by euclid_apply (helper_1_17_step7 a b c d AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show between b c d; assumption)) (by euclid_assumption "" (show ∠ a:c:d + ∠ a:c:b = ∟ + ∟; assumption)))

  euclid_sentence "1.17.8"
    "and further (that the sum of) $CAB$ and $ABC$ (is less than two right-angles). "
    (step8 : ∠ c:a:b + ∠ a:b:c < ∟ + ∟) := by euclid_apply (helper_1_17_step8 a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))

  exact step6
  euclid_conclude_sentence "1.17.9"
    "Thus, for any triangle,  (the sum of) two angles taken together in any (possible way) is less than two right-angles. (Which is) the very thing it was required to show."

end Elements.Book1
