import SystemE
import Book.Prop03
import Book.Prop11
import Book1.Prop48.step1
import Book1.Prop48.step2
import Book1.Prop48.step3
import Book1.Prop48.step4
import Book1.Prop48.step5
import Book1.Prop48.step6
import Book1.Prop48.step7
import Book1.Prop48.step8
import Book1.Prop48.step9
import Book1.Prop48.step10
import Book1.Prop48.step11
import Book1.Prop48.step12
import Book1.Prop48.step13
import Book1.Prop48.step14
import Book1.Prop48.step15
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_48 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| →
  ∠ b:a:c = ∟ := by
  euclid_intros
  euclid_intro_sentence "1.48.0"
    "For let the square on one of the sides, $BC$, of triangle $ABC$ be equal to the (sum of the) squares on the sides $BA$ and $AC$. I say that angle $BAC$ is a right-angle. "

  euclid_apply (proposition_11'' a c AC) as d'
  euclid_apply (line_from_points a d') as AD
  euclid_apply (extend_point AD d' a) as d''
  euclid_apply (extend_point_longer AD d'' a (a─b)) as d'''
  euclid_apply (proposition_3 a d''' a b AD AB) as d
  euclid_sentence "1.48.1"
    "For let $AD$ have been drawn from point $A$ at right-angles to the straight-line $AC$ [Prop.~1.11],"
    (step1 : ∠ d:a:c = ∟) := by euclid_apply (helper_1_48_step1 a b c d d' d'' d''' AB BC AC AD (by euclid_assumption "" (show ¬d'.onLine AC; assumption)) (by euclid_assumption "" (show ∠d':a:c = ∟; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d'.onLine AD; assumption)) (by euclid_assumption "" (show d''.onLine AD; assumption)) (by euclid_assumption "" (show between d' a d''; assumption)) (by euclid_assumption "" (show d'''.onLine AD; assumption)) (by euclid_assumption "" (show between d'' a d'''; assumption)) (by euclid_assumption "" (show between a d d'''; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)))

  euclid_sentence "1.48.2"
    "and let $AD$ have been made equal to $BA$ [Prop.~1.3],"
    (step2 : |(a─d)| = |(b─a)|) := by euclid_apply (helper_1_48_step2 (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)))

  euclid_apply (line_from_points d c) as DC
  euclid_sentence "1.48.3"
    "and let $DC$ have been joined."
    (step3 : distinctPointsOnLine d c DC) := by euclid_apply (helper_1_48_step3 a b c d d' d'' d''' AC AD DC (by euclid_assumption "" (show ¬d'.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d'.onLine AD; assumption)) (by euclid_assumption "" (show d'''.onLine AD; assumption)) (by euclid_assumption "" (show between a d d'''; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)))

  -- @assumption_valid
  have step4_assumption1 : |(d─a)| = |(a─b)| := by euclid_finish
  -- @assumption ("$DA$ is equal to $AB$", |(d─a)| = |(a─b)|)
  euclid_sentence "1.48.4"
    "Since $DA$ is equal to $AB$, the square on $DA$ is thus also equal to the square on $AB$."
    (step4 : |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|) := by euclid_apply (helper_1_48_step4 (by euclid_assumption "$DA$ is equal to $AB$" (show |(d─a)| = |(a─b)|; assumption)))

  euclid_sentence "1.48.5"
    "Let the square on $AC$ have been added to both."
    (step5 : |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(a─b)| * |(a─b)| + |(a─c)| * |(a─c)|) := by euclid_apply (helper_1_48_step5 (by euclid_assumption "" (show |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|; assumption)))

  euclid_sentence "1.48.6"
    "Thus, the (sum of the) squares on $DA$ and $AC$ is equal to the (sum of the) squares on $BA$ and $AC$."
    (step6 : |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|) := by euclid_apply (helper_1_48_step6 (by euclid_assumption "" (show |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|; assumption)))

  -- @assumption_valid
  have step7_assumption1 : ∠ d:a:c = ∟ := by assumption
  -- @assumption ("angle $DAC$ is a right-angle", ∠ d:a:c = ∟)
  euclid_sentence "1.48.7"
    "But, the (square) on $DC$  is equal to the (sum of the squares) on $DA$ and $AC$. For angle $DAC$ is a right-angle [Prop.~1.47]."
    (step7 : |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)|) := by euclid_apply (helper_1_48_step7 a b c d d' d'' d''' AB BC AC AD DC (by euclid_assumption "" (show ¬d'.onLine AC; assumption)) (by euclid_assumption "" (show ∠d':a:c = ∟; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d'.onLine AD; assumption)) (by euclid_assumption "" (show d''.onLine AD; assumption)) (by euclid_assumption "" (show between d' a d''; assumption)) (by euclid_assumption "" (show d'''.onLine AD; assumption)) (by euclid_assumption "" (show between d'' a d'''; assumption)) (by euclid_assumption "" (show |(a─d''')| > |(a─b)|; assumption)) (by euclid_assumption "" (show between a d d'''; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "angle $DAC$ is a right-angle" (show ∠ d:a:c = ∟; assumption)))

  -- @assumption_valid
  have step8_assumption1 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by assumption
  -- @assumption ("(that) was assumed", |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|)
  euclid_sentence "1.48.8"
    "But, the  (square) on $BC$ is equal to (sum of the squares) on $BA$ and $AC$. For (that) was assumed."
    (step8 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|) := by euclid_apply (helper_1_48_step8 (by euclid_assumption "(that) was assumed" (show |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|; assumption)))

  euclid_sentence "1.48.9"
    "Thus, the square on $DC$ is equal to the square on $BC$."
    (step9 : |(d─c)| * |(d─c)| = |(b─c)| * |(b─c)|) := by euclid_apply (helper_1_48_step9 (by euclid_assumption "" (show |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|; assumption)) (by euclid_assumption "" (show |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)|; assumption)) (by euclid_assumption "" (show |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|; assumption)))

  euclid_sentence "1.48.10"
    "So  side $DC$ is also equal to (side) $BC$."
    (step10 : |(d─c)| = |(b─c)|) := by euclid_apply (helper_1_48_step10 (by euclid_assumption "" (show |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)|; assumption)) (by euclid_assumption "" (show |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|; assumption)) (by euclid_assumption "" (show |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|; assumption)))

  -- @assumption_valid
  have step11_assumption1 : |(d─a)| = |(a─b)| := by assumption
  -- @assumption_valid
  have step11_assumption2 : distinctPointsOnLine a c AC := by euclid_finish
  -- @assumption ("$DA$ is equal to $AB$", |(d─a)| = |(a─b)|)
  -- @assumption ("$AC$ (is) common", distinctPointsOnLine a c AC)
  euclid_sentence "1.48.11"
    "And since $DA$ is equal to $AB$, and $AC$ (is) common, the two (straight-lines) $DA$, $AC$ are equal to the two (straight-lines) $BA$, $AC$."
    (step11 : |(d─a)| = |(b─a)| ∧ |(a─c)| = |(a─c)|) := by euclid_apply (helper_1_48_step11 (by euclid_assumption "$DA$ is equal to $AB$" (show |(d─a)| = |(a─b)|; assumption)) (by euclid_assumption "$AC$ (is) common" (show distinctPointsOnLine a c AC; assumption)))

  euclid_sentence "1.48.12"
    "And the base $DC$ is equal to the base $BC$."
    (step12 : |(d─c)| = |(b─c)|) := by euclid_apply (helper_1_48_step12 (by euclid_assumption "" (show |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)|; assumption)) (by euclid_assumption "" (show |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|; assumption)) (by euclid_assumption "" (show |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|; assumption)))

  euclid_sentence "1.48.13"
    "Thus, angle $DAC$ [is] equal to angle $BAC$ [Prop.~1.8]. "
    (step13 : ∠ d:a:c = ∠ b:a:c) := by euclid_apply (helper_1_48_step13 a b c d d' d'' d''' AB BC AC AD DC (by euclid_assumption "" (show ¬d'.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d'.onLine AD; assumption)) (by euclid_assumption "" (show d''.onLine AD; assumption)) (by euclid_assumption "" (show between d' a d''; assumption)) (by euclid_assumption "" (show d'''.onLine AD; assumption)) (by euclid_assumption "" (show between d'' a d'''; assumption)) (by euclid_assumption "" (show between a d d'''; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show |(d─c)| = |(b─c)|; assumption)))

  euclid_sentence "1.48.14"
    "But $DAC$ is a right-angle."
    (step14 : ∠ d:a:c = ∟) := by euclid_apply (helper_1_48_step14 (by euclid_assumption "" (show ∠ d:a:c = ∟; assumption)))

  euclid_sentence "1.48.15"
    "Thus, $BAC$ is also a right-angle. "
    (step15 : ∠ b:a:c = ∟) := by euclid_apply (helper_1_48_step15 (by euclid_assumption "" (show ∠ d:a:c = ∠ b:a:c; assumption)) (by euclid_assumption "" (show ∠ d:a:c = ∟; assumption)))

  exact step15
  euclid_conclude_sentence "1.48.16"
    "Thus, if the square on one of the sides of a triangle is equal to the (sum of the) squares on the remaining two sides of the triangle then the angle contained by the remaining two sides of the triangle is a right-angle. (Which is) the very thing it was required to show."

end Elements.Book1
