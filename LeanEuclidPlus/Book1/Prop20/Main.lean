import SystemE
import Book1.Prop03.Main
import Book1.Prop20.step1
import Book1.Prop20.step2
import Book1.Prop20.step3
import Book1.Prop20.step4
import Book1.Prop20.step5
import Book1.Prop20.step6
import Book1.Prop20.step7
import Book1.Prop20.step8
import Book1.Prop20.step9
import Book1.Prop20.step10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_20 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC →
  |(b─a)| + |(a─c)| > |(b─c)| ∧
  |(a─b)| + |(b─c)| > |(a─c)| ∧
  |(b─c)| + |(c─a)| > |(a─b)| := by
  euclid_intros
  euclid_intro_sentence "1.20.0"
    "In any triangle, (the sum of) two sides taken together in any (possible way) is greater than the remaining (side). For let $ABC$ be a triangle. I say that in triangle $ABC$ (the sum of) two sides taken together in any (possible way) is greater than the remaining (side). (So), (the sum of) $BA$ and $AC$ (is greater) than $BC$, (the sum of) $AB$ and $BC$ than $AC$, and (the sum of) $BC$ and $CA$ than $AB$. "

  euclid_apply (extend_point_longer AB b a (c─a)) as d'
  euclid_apply (proposition_3 a d' a c AB AC) as d
  euclid_sentence "1.20.1"
    "For let $BA$ have been drawn through to point $D$,"
    (step1 : between b a d) := by euclid_apply (helper_1_20_step1 b a d d' AB (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show d'.onLine AB; assumption)) (by euclid_assumption "" (show between b a d'; assumption)) (by euclid_assumption "" (show between a d d'; assumption)))

  euclid_sentence "1.20.2"
    "and let $AD$ be made equal to $CA$ [Prop.~1.3],"
    (step2 : |(a─d)| = |(c─a)|) := by euclid_apply (helper_1_20_step2 a c d (by euclid_assumption "" (show |(a─d)| = |(a─c)|; assumption)))

  euclid_apply (line_from_points d c) as DC
  euclid_sentence "1.20.3"
    "and let $DC$ have been joined. "
    (step3 : distinctPointsOnLine d c DC) := by euclid_apply (helper_1_20_step3 a b c d d' AB BC DC (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d'.onLine AB; assumption)) (by euclid_assumption "" (show between a d d'; assumption)) (by euclid_assumption "" (show between b a d; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)))

  -- @assumption_valid
  have step4_assumption1 : |(d─a)| = |(a─c)| := by euclid_finish
  -- @assumption ("$DA$ is equal to $AC$", |(d─a)| = |(a─c)|)
  euclid_sentence "1.20.4"
    "Therefore, since $DA$ is equal to $AC$, the angle $ADC$ is also equal to $ACD$ [Prop.~1.5]."
    (step4 : ∠ a:d:c = ∠ a:c:d) := by euclid_apply (helper_1_20_step4 a b c d d' AB BC AC DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d'.onLine AB; assumption)) (by euclid_assumption "" (show between a d d'; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "$DA$ is equal to $AC$" (show |(d─a)| = |(a─c)|; assumption)))

  euclid_sentence "1.20.5"
    "Thus, $BCD$ is greater than $ADC$."
    (step5 : ∠ b:c:d > ∠ a:d:c) := by euclid_apply (helper_1_20_step5 a b c d d' AB BC AC DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d'.onLine AB; assumption)) (by euclid_assumption "" (show between a d d'; assumption)) (by euclid_assumption "" (show between b a d; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show ∠ a:d:c = ∠ a:c:d; assumption)))

  -- @assumption_valid
  have step6_assumption1 : ∠ b:c:d > ∠ b:d:c := by euclid_finish
  -- @assumption ("$DCB$ is a triangle having the angle $BCD$ greater than $BDC$", ∠ b:c:d > ∠ b:d:c)
  euclid_sentence "1.20.6"
    "And since  $DCB$ is a triangle having the angle $BCD$ greater than $BDC$, and the greater angle subtends the greater side [Prop.~1.19], $DB$ is thus greater than $BC$."
    (step6 : |(d─b)| > |(b─c)|) := by euclid_apply (helper_1_20_step6 a b c d d' AB BC AC DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d'.onLine AB; assumption)) (by euclid_assumption "" (show between a d d'; assumption)) (by euclid_assumption "" (show between b a d; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "$DCB$ is a triangle having the angle $BCD$ greater than $BDC$" (show ∠ b:c:d > ∠ b:d:c; assumption)))

  euclid_sentence "1.20.7"
    "But $DA$ is equal to $AC$."
    (step7 : |(d─a)| = |(a─c)|) := by euclid_apply (helper_1_20_step7 a c d (by euclid_assumption "" (show |(d─a)| = |(a─c)|; assumption)))

  euclid_sentence "1.20.8"
    "Thus, (the sum of) $BA$ and $AC$ is greater than $BC$."
    (step8 : |(b─a)| + |(a─c)| > |(b─c)|) := by euclid_apply (helper_1_20_step8 a b c d (by euclid_assumption "" (show between b a d; assumption)) (by euclid_assumption "" (show |(d─b)| > |(b─c)|; assumption)) (by euclid_assumption "" (show |(d─a)| = |(a─c)|; assumption)))

  euclid_sentence "1.20.9"
    "Similarly, we can show that (the sum of) $AB$ and $BC$ is also greater than $CA$,"
    (step9 : |(a─b)| + |(b─c)| > |(a─c)|) := by euclid_apply (helper_1_20_step9 a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))

  euclid_sentence "1.20.10"
    "and (the sum of) $BC$ and $CA$ than $AB$. "
    (step10 : |(b─c)| + |(c─a)| > |(a─b)|) := by euclid_apply (helper_1_20_step10 a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))

  exact ⟨step8, step9, step10⟩
  euclid_conclude_sentence "1.20.11"
    "Thus, in any triangle, (the sum of) two sides taken together in any (possible way) is greater than the remaining (side). (Which is) the very thing it was required to show."

end Elements.Book1
