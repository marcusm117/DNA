import SystemE
import Book1.Prop03.Main
import Book1.Prop10.Main
import Mathlib.Tactic.Linarith
import Book1.Prop16.step1
import Book1.Prop16.step2
import Book1.Prop16.step3
import Book1.Prop16.step4
import Book1.Prop16.step5
import Book1.Prop16.step6
import Book1.Prop16.step7
import Book1.Prop16.step8
import Book1.Prop16.step9
import Book1.Prop16.step10
import Book1.Prop16.step11
import Book1.Prop16.step12
import Book1.Prop16.step13
import Book1.Prop16.step14
import Book1.Prop16.h1
import Book1.Prop16.h2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_16 : ∀ (a b c d : Point) (AB BC AC: Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  (∠ a:c:d > ∠ c:b:a) ∧ (∠ a:c:d > ∠ b:a:c) := by
  euclid_intros
  euclid_intro_sentence "1.16.0"
    "For any triangle, when one of the sides is produced, the external angle is greater than each of the internal and opposite angles.  Let $ABC$ be a triangle, and let one of its sides $BC$ have been produced   to $D$. I say that the external angle $ACD$ is greater than each of the  internal and opposite angles, $CBA$ and $BAC$.   "

  euclid_apply (proposition_10 a c AC) as e
  euclid_sentence "1.16.1"
    "Let the (straight-line) $AC$ have been cut in half at (point) $E$ [Prop.~1.10]. "
    (step1 : between a e c ∧ |(a─e)| = |(e─c)|) := by euclid_apply (helper_1_16_step1 a e c (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)))

  euclid_apply (line_from_points b e) as BE
  euclid_apply (extend_point_longer BE b e (b─e)) as f'
  euclid_apply (proposition_3 e f' b e BE BE) as f
  -- @assumption_valid
  have step2_assumption1 : distinctPointsOnLine b e BE := by euclid_finish
  -- @assumption ("$BE$ being joined", distinctPointsOnLine b e BE)
  euclid_sentence "1.16.2"
    "And $BE$ being joined, let it have been produced in a straight-line to  (point) $F$."
    (step2 : between b e f) := by euclid_apply (helper_1_16_step2 b e f f' BE (by euclid_assumption "" (show between b e f'; assumption)) (by euclid_assumption "" (show between e f f'; assumption)) (by euclid_assumption "$BE$ being joined" (show distinctPointsOnLine b e BE; assumption)))

  euclid_sentence "1.16.3"
    "And let $EF$ be made equal to $BE$ [Prop.~1.3],"
    (step3 : |(e─f)| = |(b─e)|) := by euclid_apply (helper_1_16_step3 b e f (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)))

  euclid_apply (line_from_points f c) as FC
  euclid_sentence "1.16.4"
    "and let $FC$ have been joined,"
    (step4 : distinctPointsOnLine f c FC) := by euclid_apply (helper_1_16_step4 a b c e f AC BC AB BE FC (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show between b e f; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)))

  euclid_apply (extend_point AC a c) as g
  euclid_sentence "1.16.5"
    "and let $AC$ have been drawn through to (point) $G$.  "
    (step5 : between a c g) := by euclid_apply (helper_1_16_step5 a c g (by euclid_assumption "" (show between a c g; assumption)))

  -- @assumption_valid
  have step6_assumption1 : |(a─e)| = |(e─c)| := by assumption
  -- @assumption_valid
  have step6_assumption2 : |(b─e)| = |(e─f)| := by linarith
  -- @assumption ("$AE$ is equal to $EC$", |(a─e)| = |(e─c)|)
  -- @assumption ("$BE$ to $EF$", |(b─e)| = |(e─f)|)
  euclid_sentence "1.16.6"
    "Therefore, since $AE$ is equal to $EC$, and $BE$ to $EF$, the two (straight-lines)  $AE$, $EB$ are equal to the two (straight-lines) $CE$, $EF$, respectively.  "
    (step6 : |(a─e)| = |(c─e)| ∧ |(b─e)| = |(e─f)|) := by euclid_apply (helper_1_16_step6 a b c e f (by euclid_assumption "$AE$ is equal to $EC$" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "$BE$ to $EF$" (show |(b─e)| = |(e─f)|; assumption)))

  euclid_sentence "1.16.7"
    "Also, angle $AEB$ is equal to angle $FEC$, for (they are)  vertically opposite [Prop.~1.15]."
    (step7 : ∠ a:e:b = ∠ f:e:c) := by euclid_apply (helper_1_16_step7 a b c e f AB BC AC BE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between b e f; assumption)))

  euclid_sentence "1.16.8"
    "Thus, the base $AB$ is equal to the base  $FC$,"
    (step8 : |(a─b)| = |(f─c)|) := by euclid_apply (helper_1_16_step8 a b c e f AB BC AC BE FC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between b e f; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(b─e)| = |(e─f)|; assumption)) (by euclid_assumption "" (show ∠ a:e:b = ∠ f:e:c; assumption)))

  euclid_sentence "1.16.9"
    "and the triangle $ABE$ is equal to the triangle $FEC$,"
    (step9 : Triangle.area △ a:b:e = Triangle.area △ f:e:c) := by euclid_apply (helper_1_16_step9 a b c e f AB BC AC BE FC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between b e f; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(b─e)| = |(e─f)|; assumption)) (by euclid_assumption "" (show ∠ a:e:b = ∠ f:e:c; assumption)))

  euclid_sentence "1.16.10"
    "and the remaining  angles subtended by the equal sides are equal to the corresponding remaining angles [Prop.~1.4]."
    (step10 : (∠ b:a:e = ∠ e:c:f) ∧ (∠ a:b:e = ∠ c:f:e)) := by euclid_apply (helper_1_16_step10 a b c e f AB BC AC BE FC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between b e f; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(b─e)| = |(e─f)|; assumption)) (by euclid_assumption "" (show ∠ a:e:b = ∠ f:e:c; assumption)))

  euclid_sentence "1.16.11"
    "Thus, $BAE$ is equal to $ECF$."
    (step11 : ∠ b:a:e = ∠ e:c:f) := by euclid_apply (helper_1_16_step11 a b c e f (by euclid_assumption "" (show (∠ b:a:e = ∠ e:c:f) ∧ (∠ a:b:e = ∠ c:f:e); assumption)))

  euclid_sentence "1.16.12"
    "But $ECD$ is greater than $ECF$."
    (step12 : ∠ e:c:d > ∠ e:c:f) := by euclid_apply (helper_1_16_step12 a b c d e f AB BC AC BE FC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show between b c d; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between b e f; assumption)) (by euclid_assumption "" (show ∠ a:e:b = ∠ f:e:c; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ e:c:f; assumption)))

  euclid_sentence "1.16.13"
    "Thus,  $ACD$ is greater than $BAE$."
    (step13 : ∠ a:c:d > ∠ b:a:e) := by euclid_apply (helper_1_16_step13 a b c d e f AC BC (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between b c d; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ e:c:f; assumption)) (by euclid_assumption "" (show ∠ e:c:d > ∠ e:c:f; assumption)))

  euclid_sentence "1.16.14"
    "Similarly, by having cut $BC$ in half,  it can  be shown (that) $BCG$---that is to say, $ACD$---(is) also greater than $ABC$."
    (step14 : ∠ a:c:d > ∠ a:b:c) := by euclid_apply (helper_1_16_step14 a b c d g AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between b c d; assumption)) (by euclid_assumption "" (show between a c g; assumption)) (by euclid_assumption "" (show g.onLine AC; assumption)))

  -- ∠ c:b:a = ∠ a:b:c (step14) and ∠ b:a:e = ∠ b:a:c (e between a and c)
  have h1 : ∠ a:c:d > ∠ c:b:a := by euclid_apply (helper_1_16_h1 a b c d AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ a:c:d > ∠ a:b:c; assumption)))
  have h2 : ∠ a:c:d > ∠ b:a:c := by euclid_apply (helper_1_16_h2 a b c d e AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show ∠ a:c:d > ∠ b:a:e; assumption)))
  exact ⟨h1, h2⟩
  euclid_conclude_sentence "1.16.15"
    "Thus, for any triangle, when one of the sides is produced, the external angle is greater than each of the internal and opposite angles. (Which is) the very thing it was required to show."

end Elements.Book1
