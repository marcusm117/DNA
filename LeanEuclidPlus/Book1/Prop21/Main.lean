import SystemE
import Book1.Prop21.step1
import Book1.Prop21.step2
import Book1.Prop21.step3
import Book1.Prop21.step4
import Book1.Prop21.step5
import Book1.Prop21.step6
import Book1.Prop21.step7
import Book1.Prop21.step8
import Book1.Prop21.step9
import Book1.Prop21.step10
import Book1.Prop21.step11
import Book1.Prop21.step12
import Book1.Prop21.step5_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_21 : ∀ (a b c d : Point) (AB BC AC BD DC : Line),
  formTriangle a b c AB BC AC ∧ (a.sameSide d BC) ∧ (c.sameSide d AB) ∧ (b.sameSide d AC) ∧
  distinctPointsOnLine b d BD ∧ distinctPointsOnLine d c DC →
  (|(b─d)| + |(d─c)| < |(b─a)| + |(a─c)|) ∧ (∠ b:d:c > ∠ b:a:c) := by
  euclid_intros
  euclid_intro_sentence "1.21.0"
    "If two internal straight-lines are constructed on one of the sides of a triangle, from its ends,  the constructed (straight-lines) will be less than the two remaining  sides of the triangle, but will encompass a greater angle. For let the two internal straight-lines $BD$ and $DC$ have been constructed on one of the sides $BC$ of the triangle $ABC$, from its ends $B$ and $C$ (respectively). I say that  $BD$ and $DC$ are less than the (sum of the) two  remaining sides of the triangle $BA$ and $AC$, but encompass an angle $BDC$ greater than $BAC$. "

  euclid_apply (intersection_lines BD AC) as e
  euclid_sentence "1.21.1"
    "For let $BD$ have been drawn through to $E$."
    (step1 : between b d e ∧ e.onLine BD) := by euclid_apply (helper_1_21_step1 a b c d e AB BC AC BD DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine AC; assumption)) (by euclid_assumption "" (show b.sameSide d AC; assumption)) (by euclid_assumption "" (show a.sameSide d BC; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)))

  euclid_sentence "1.21.2"
    "And since in any triangle (the sum of any) two sides is greater than the remaining (side) [Prop.~1.20],  in triangle $ABE$ the  (sum of the) two sides $AB$ and $AE$ is thus  greater than $BE$."
    (step2 : |(a─b)| + |(a─e)| > |(b─e)|) := by euclid_apply (helper_1_21_step2 a b c d e AB BC AC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine AC; assumption)) (by euclid_assumption "" (show b.sameSide d AC; assumption)) (by euclid_assumption "" (show a.sameSide d BC; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)))

  euclid_sentence "1.21.3"
    "Let $EC$ have been added to both."
    (step3 : |(a─b)| + |(a─e)| + |(e─c)| > |(b─e)| + |(e─c)|) := by euclid_apply (helper_1_21_step3 a b c e (by euclid_assumption "" (show |(a─b)| + |(a─e)| > |(b─e)|; assumption)))

  euclid_sentence "1.21.4"
    "Thus, (the sum of) $BA$ and $AC$ is greater than (the sum of) $BE$ and $EC$. "
    (step4 : |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)|) := by euclid_apply (helper_1_21_step4 a b c d e AB BC AC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine AC; assumption)) (by euclid_assumption "" (show b.sameSide d AC; assumption)) (by euclid_assumption "" (show a.sameSide d BC; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show between b d e ∧ e.onLine BD; assumption)) (by euclid_assumption "" (show |(a─b)| + |(a─e)| + |(e─c)| > |(b─e)| + |(e─c)|; assumption)))

  -- @assumption_gap
  have step5_assumption1 : |(c─e)| + |(e─d)| > |(c─d)| := by euclid_apply (helper_1_21_step5_assumption1 a b c d e AB BC AC BD DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show b.sameSide d AC; assumption)) (by euclid_assumption "" (show a.sameSide d BC; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)))
  -- @assumption ("$CE$ and $ED$ is  greater than $CD$", |(c─e)| + |(e─d)| > |(c─d)|)
  euclid_sentence "1.21.5"
    "Again, since in triangle $CED$ the (sum of the) two sides $CE$ and $ED$ is  greater than $CD$, let $DB$ have been added to both."
    (step5 : |(c─e)| + |(e─d)| + |(d─b)| > |(c─d)| + |(d─b)|) := by euclid_apply (helper_1_21_step5 b c d e (by euclid_assumption "$CE$ and $ED$ is  greater than $CD$" (show |(c─e)| + |(e─d)| > |(c─d)|; assumption)))

  euclid_sentence "1.21.6"
    "Thus,  (the sum of) $CE$ and $EB$ is greater than  (the sum of) $CD$ and $DB$."
    (step6 : |(c─e)| + |(e─b)| > |(c─d)| + |(d─b)|) := by euclid_apply (helper_1_21_step6 b c d e (by euclid_assumption "" (show between b d e ∧ e.onLine BD; assumption)) (by euclid_assumption "" (show |(c─e)| + |(e─d)| + |(d─b)| > |(c─d)| + |(d─b)|; assumption)))

  euclid_sentence "1.21.7"
    "But, (the sum of) $BA$ and $AC$ was shown (to be) greater than (the sum of) $BE$  and $EC$."
    (step7 : |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)|) := by euclid_apply (helper_1_21_step7 a b c e (by euclid_assumption "" (show |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)|; assumption)))

  euclid_sentence "1.21.8"
    "Thus, (the sum of) $BA$ and $AC$ is much greater than (the sum of) $BD$ and $DC$. "
    (step8 : |(b─a)| + |(a─c)| > |(b─d)| + |(d─c)|) := by euclid_apply (helper_1_21_step8 a b c d e (by euclid_assumption "" (show |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)|; assumption)) (by euclid_assumption "" (show |(c─e)| + |(e─b)| > |(c─d)| + |(d─b)|; assumption)))

  -- Prop 1.16 is a theorem citation; no local assumption needed
  euclid_sentence "1.21.9"
    "Again, since in any  triangle the external angle  is greater than the internal and opposite (angles) [Prop. 1.16],  in triangle $CDE$ the external angle $BDC$ is thus greater than $CED$. "
    (step9 : ∠ b:d:c > ∠ c:e:d) := by euclid_apply (helper_1_21_step9 a b c d e AB BC AC BD DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show b.sameSide d AC; assumption)) (by euclid_assumption "" (show a.sameSide d BC; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show between b d e ∧ e.onLine BD; assumption)))

  euclid_sentence "1.21.10"
    "Accordingly, for the same (reason),  the external angle $CEB$ of the triangle $ABE$ is also greater than $BAC$."
    (step10 : ∠ c:e:b > ∠ b:a:c) := by euclid_apply (helper_1_21_step10 a b c d e AB BC AC BD DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show b.sameSide d AC; assumption)) (by euclid_assumption "" (show a.sameSide d BC; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show between b d e ∧ e.onLine BD; assumption)))

  euclid_sentence "1.21.11"
    "But, $BDC$ was shown (to be)  greater than $CEB$."
    (step11 : ∠ b:d:c > ∠ c:e:b) := by euclid_apply (helper_1_21_step11 a b c d e AB BC AC BD DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show b.sameSide d AC; assumption)) (by euclid_assumption "" (show a.sameSide d BC; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show between b d e ∧ e.onLine BD; assumption)) (by euclid_assumption "" (show ∠ b:d:c > ∠ c:e:d; assumption)))

  euclid_sentence "1.21.12"
    "Thus, $BDC$ is much greater than $BAC$. "
    (step12 : ∠ b:d:c > ∠ b:a:c) := by euclid_apply (helper_1_21_step12 a b c d e (by euclid_assumption "" (show ∠ c:e:b > ∠ b:a:c; assumption)) (by euclid_assumption "" (show ∠ b:d:c > ∠ c:e:b; assumption)))

  exact ⟨step8, step12⟩
  euclid_conclude_sentence "1.21.13"
    "Thus, if two internal straight-lines are constructed on one of the sides of a triangle, from its ends,  the constructed (straight-lines) are less than the two remaining  sides of the triangle, but  encompass a greater angle. (Which is) the very thing it was required to show."

end Elements.Book1
