import SystemE
import Book1.Prop19.step1
import Book1.Prop19.step3
import Book1.Prop19.step4
import Book1.Prop19.step5
import Book1.Prop19.step7
import Book1.Prop19.step8
import Book1.Prop19.step9
import Book1.Prop19.step10
import Book1.Prop19.step11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_19 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c > ∠ b:c:a) →
  (|(a─c)| > |(a─b)|) := by
  euclid_intros
  euclid_intro_sentence "1.19.0"
    "In any triangle, the greater angle is subtended by the greater side. Let $ABC$ be a triangle having the angle $ABC$ greater than $BCA$. I say that side $AC$ is also greater than side $AB$. "

  by_contra h_notgt
  -- h_notgt : ¬(|(a─c)| > |(a─b)|); goal: False

  euclid_sentence "1.19.1"
    "For if not, $AC$ is certainly either equal to, or less than, $AB$."
    (step1 : |(a─c)| = |(a─b)| ∨ |(a─c)| < |(a─b)|) := by euclid_apply (helper_1_19_step1 (by euclid_assumption "" (show ¬|(a─c)| > |(a─b)|; assumption)))

  euclid_wts "1.19.2"
    "In fact, $AC$ is not equal to $AB$."
  have hne : |(a─c)| ≠ |(a─b)| := by
    intro h_eq
    euclid_sentence "1.19.3"
      "For then angle $ABC$  would also have been equal to $ACB$ [Prop.~1.5]."
      (step3 : ∠ a:b:c = ∠ b:c:a) := by euclid_apply (helper_1_19_step3 a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)))
    euclid_sentence "1.19.4"
      "But it is not."
      (step4 : False) := by euclid_apply (helper_1_19_step4 (by euclid_assumption "" (show ∠ a:b:c > ∠ b:c:a; assumption)) (by euclid_assumption "" (show ∠ a:b:c = ∠ b:c:a; assumption)))
    exact step4

  euclid_sentence "1.19.5"
    "Thus, $AC$ is not equal to $AB$."
    (step5 : |(a─c)| ≠ |(a─b)|) := by euclid_apply (helper_1_19_step5 (by euclid_assumption "" (show |(a─c)| ≠ |(a─b)|; assumption)))

  euclid_wts "1.19.6"
    "Neither, indeed, is $AC$ less than $AB$."
  have hnlt : ¬(|(a─c)| < |(a─b)|) := by
    intro h_lt
    euclid_sentence "1.19.7"
      "For then angle $ABC$ would also have been less than $ACB$ [Prop.~1.18]."
      (step7 : ∠ a:b:c < ∠ b:c:a) := by euclid_apply (helper_1_19_step7 a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(a─c)| < |(a─b)|; assumption)))
    euclid_sentence "1.19.8"
      "But it is not."
      (step8 : False) := by euclid_apply (helper_1_19_step8 (by euclid_assumption "" (show ∠ a:b:c > ∠ b:c:a; assumption)) (by euclid_assumption "" (show ∠ a:b:c < ∠ b:c:a; assumption)))
    exact step8

  euclid_sentence "1.19.9"
    "Thus, $AC$ is not less than $AB$."
    (step9 : ¬(|(a─c)| < |(a─b)|)) := by euclid_apply (helper_1_19_step9 (by euclid_assumption "" (show ¬(|(a─c)| < |(a─b)|); assumption)))

  -- @assumption_valid
  have step10_assumption1 : |(a─c)| ≠ |(a─b)| := by assumption
  -- @assumption ("($AC$) is    not equal (to $AB$)", |(a─c)| ≠ |(a─b)|)
  euclid_sentence "1.19.10"
    "But it was  shown that ($AC$) is    not equal (to $AB$) either."
    (step10 : |(a─c)| ≠ |(a─b)|) := by euclid_apply (helper_1_19_step10 (by euclid_assumption "($AC$) is    not equal (to $AB$)" (show |(a─c)| ≠ |(a─b)|; assumption)))

  euclid_sentence "1.19.11"
    "Thus, $AC$  is greater than $AB$."
    (step11 : |(a─c)| > |(a─b)|) := by euclid_apply (helper_1_19_step11 (by euclid_assumption "" (show |(a─c)| ≠ |(a─b)|; assumption)) (by euclid_assumption "" (show ¬(|(a─c)| < |(a─b)|); assumption)))

  exact h_notgt step11
  euclid_conclude_sentence "1.19.12"
    "Thus, in any triangle, the greater angle is subtended by the greater side. (Which is) the very thing it was required to show."

end Elements.Book1
