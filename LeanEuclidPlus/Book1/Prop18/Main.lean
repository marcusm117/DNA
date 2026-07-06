import SystemE
import Book1.Prop03.Main
import Book1Variants.Prop05
import Book1.Prop16.Main
import Mathlib.Tactic.Linarith
import Book1.Prop18.step1
import Book1.Prop18.step2
import Book1.Prop18.step3
import Book1.Prop18.step4
import Book1.Prop18.step5
import Book1.Prop18.step6
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_18 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─c)| > |(a─b)|) →
  (∠ a:b:c > ∠ b:c:a) := by
  euclid_intros
  euclid_intro_sentence "1.18.0"
    "In any triangle, the greater side subtends the greater angle. For let $ABC$ be a triangle having side $AC$ greater than $AB$. I say that angle $ABC$ is also greater than $BCA$. "

  euclid_apply (proposition_3 a c a b AC AB) as d
  euclid_sentence "1.18.1"
    "For since $AC$ is greater than $AB$, let $AD$ be made equal to $AB$  [Prop.~1.3],"
    (step1 : |(a─d)| = |(a─b)|) := by euclid_apply (helper_1_18_step1 a b d (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)))

  euclid_apply (line_from_points b d) as BD
  euclid_sentence "1.18.2"
    "and let $BD$ have been joined. "
    (step2 : distinctPointsOnLine b d BD) := by euclid_apply (helper_1_18_step2 a b c d AB BC AC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)))

  -- @assumption_valid
  have step3_assumption1 : between a d c := by assumption
  -- @assumption ("angle $ADB$ is external to triangle $BCD$", between a d c)
  euclid_sentence "1.18.3"
    "And since angle $ADB$ is external to triangle $BCD$, it is greater than the internal and opposite (angle) $DCB$ [Prop.~1.16]."
    (step3 : ∠ a:d:b > ∠ d:c:b) := by euclid_apply (helper_1_18_step3 a b c d AB BC AC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "angle $ADB$ is external to triangle $BCD$" (show between a d c; assumption)))

  -- @assumption_valid
  have step4_assumption1 : |(a─b)| = |(a─d)| := by linarith
  -- @assumption ("$AB$ is also equal to side $AD$", |(a─b)| = |(a─d)|)
  euclid_sentence "1.18.4"
    "But $ADB$ (is) equal to $ABD$, since side $AB$ is also equal to side $AD$ [Prop.~1.5]."
    (step4 : ∠ a:d:b = ∠ a:b:d) := by euclid_apply (helper_1_18_step4 a b d AB BC AC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "$AB$ is also equal to side $AD$" (show |(a─b)| = |(a─d)|; assumption)))

  euclid_sentence "1.18.5"
    "Thus, $ABD$ is also greater than $ACB$."
    (step5 : ∠ a:b:d > ∠ b:c:a) := by euclid_apply (helper_1_18_step5 a b c d BC AC (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ∠ a:d:b > ∠ d:c:b; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∠ a:b:d; assumption)))

  euclid_sentence "1.18.6"
    "Thus, $ABC$ is much greater than  $ACB$. "
    (step6 : ∠ a:b:c > ∠ b:c:a) := by euclid_apply (helper_1_18_step6 a b c d AB BC AC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:c:a; assumption)))

  exact step6
  euclid_conclude_sentence "1.18.7"
    "Thus, in any triangle, the greater side subtends the greater angle. (Which is) the very thing  it was required to show."

end Elements.Book1
