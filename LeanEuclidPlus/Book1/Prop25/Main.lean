import SystemE
import Book1.Prop25.step1
import Book1.Prop25.step3
import Book1.Prop25.step4
import Book1.Prop25.step5
import Book1.Prop25.step7
import Book1.Prop25.step8
import Book1.Prop25.step9
import Book1.Prop25.step10
import Book1.Prop25.step11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_25 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (|(b─c)| > |(e─f)|) →
  (∠ b:a:c > ∠ e:d:f) := by
  euclid_intros
  euclid_intro_sentence "1.25.0"
    "If two triangles have two sides equal to two sides, respectively, but (one) has a base greater than the base (of the other), then (the former triangle) will also have the angle encompassed by the equal straight-lines greater than the (corresponding) angle (in the latter).  Let $ABC$ and $DEF$ be  two triangles having the two sides $AB$ and $AC$ equal to the two sides $DE$ and $DF$, respectively (That is), $AB$ (equal) to $DE$, and $AC$ to $DF$. And let the base $BC$ be greater than the base $EF$. I say that angle $BAC$ is also greater than $EDF$. "

  by_contra h_notgt
  -- h_notgt : ¬(∠ b:a:c > ∠ e:d:f); goal: False

  euclid_sentence "1.25.1"
    "For if not, ($BAC$) is certainly either equal to, or less than, ($EDF$)."
    (step1 : ∠ b:a:c = ∠ e:d:f ∨ ∠ b:a:c < ∠ e:d:f) := by euclid_apply (helper_1_25_step1 (by euclid_assumption "" (show ¬∠ b:a:c > ∠ e:d:f; assumption)))

  euclid_wts "1.25.2"
    "In fact, $BAC$ is not equal to $EDF$."
  have hne : ∠ b:a:c ≠ ∠ e:d:f := by
    intro h_eq
    euclid_sentence "1.25.3"
      "For then the base $BC$ would also have been equal to the base $EF$ [Prop.~1.4]."
      (step3 : |(b─c)| = |(e─f)|) := by euclid_apply (helper_1_25_step3 a b c d e f AB BC AC DE EF DF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show DE ≠ EF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show |(a─b)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(d─f)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∠ e:d:f; assumption)))
    euclid_sentence "1.25.4"
      "But it is not."
      (step4 : False) := by euclid_apply (helper_1_25_step4 (by euclid_assumption "" (show |(b─c)| > |(e─f)|; assumption)) (by euclid_assumption "" (show |(b─c)| = |(e─f)|; assumption)))
    exact step4

  euclid_sentence "1.25.5"
    "Thus, angle $BAC$ is not equal to $EDF$."
    (step5 : ∠ b:a:c ≠ ∠ e:d:f) := by euclid_apply (helper_1_25_step5 (by euclid_assumption "" (show ∠ b:a:c ≠ ∠ e:d:f; assumption)))

  euclid_wts "1.25.6"
    "Neither, indeed, is $BAC$ less than $EDF$."
  have hnlt : ¬(∠ b:a:c < ∠ e:d:f) := by
    intro h_lt
    euclid_sentence "1.25.7"
      "For then the base $BC$ would also have been less than the base $EF$ [Prop.~1.24]."
      (step7 : |(b─c)| < |(e─f)|) := by euclid_apply (helper_1_25_step7 a b c d e f AB BC AC DE EF DF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show DE ≠ EF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show |(a─b)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(d─f)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c < ∠ e:d:f; assumption)))
    euclid_sentence "1.25.8"
      "But it is not."
      (step8 : False) := by euclid_apply (helper_1_25_step8 (by euclid_assumption "" (show |(b─c)| > |(e─f)|; assumption)) (by euclid_assumption "" (show |(b─c)| < |(e─f)|; assumption)))
    exact step8

  euclid_sentence "1.25.9"
    "Thus, angle $BAC$ is not less than $EDF$."
    (step9 : ¬(∠ b:a:c < ∠ e:d:f)) := by euclid_apply (helper_1_25_step9 (by euclid_assumption "" (show ¬(∠ b:a:c < ∠ e:d:f); assumption)))

  euclid_sentence "1.25.10"
    "But it was  shown that ($BAC$ is) not equal (to $EDF$) either."
    (step10 : ∠ b:a:c ≠ ∠ e:d:f) := by euclid_apply (helper_1_25_step10 (by euclid_assumption "" (show ∠ b:a:c ≠ ∠ e:d:f; assumption)))

  euclid_sentence "1.25.11"
    "Thus, $BAC$ is greater than $EDF$. "
    (step11 : ∠ b:a:c > ∠ e:d:f) := by euclid_apply (helper_1_25_step11 (by euclid_assumption "" (show ∠ b:a:c ≠ ∠ e:d:f; assumption)) (by euclid_assumption "" (show ¬(∠ b:a:c < ∠ e:d:f); assumption)))

  exact h_notgt step11
  euclid_conclude_sentence "1.25.12"
    "Thus, if two triangles have two sides equal to two sides, respectively, but (one) has a base greater than the base (of the other), then (the former triangle) will also have the angle encompassed by the equal straight-lines greater than the (corresponding) angle (in the latter). (Which is) the very thing it was required to show."

end Elements.Book1
