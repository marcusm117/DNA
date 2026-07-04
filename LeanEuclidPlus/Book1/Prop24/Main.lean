import SystemE
import Book.Prop03
import Book.Prop23
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_24 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c > ∠ e:d:f) →
  |(b─c)| > |(e─f)| := by
  euclid_intros
  euclid_intro_sentence "1.24.0"
    "If two triangles have two sides equal to two sides, respectively,  but (one) has the angle encompassed by the equal straight-lines greater than the (corresponding)  angle (in the other), then (the former triangle) will also have a base greater than the base (of the latter).  Let  $ABC$ and $DEF$ be two triangles having the two sides $AB$ and $AC$  equal to the two sides $DE$ and $DF$, respectively. (That is), $AB$ (equal) to $DE$, and  $AC$ to $DF$.  Let them also have the angle at $A$ greater than the angle at $D$.  I say that the base $BC$ is also greater than the base $EF$. "

  euclid_apply (proposition_23' d e a b c f DE AB AC) as g'
  euclid_apply (line_from_points d g') as DG
  euclid_apply (extend_point_longer DG d g' (a─c)) as g''
  euclid_apply (proposition_3 d g'' a c DG AC) as g
  -- @assumption_valid
  have step1_assumption1 : ∠ b:a:c > ∠ e:d:f := by assumption
  -- @assumption ("angle $BAC$ is greater than angle $EDF$", ∠ b:a:c > ∠ e:d:f)
  euclid_sentence "1.24.1"
    "For since angle $BAC$ is greater than angle $EDF$, let (angle) $EDG$, equal to  angle $BAC$,  have been constructed at  the point $D$ on the straight-line $DE$ [Prop.~1.23]."
    (step1 : ∠ e:d:g = ∠ b:a:c) := by sorry

  euclid_sentence "1.24.2"
    "And let $DG$ be made equal to either of $AC$ or $DF$ [Prop.~1.3],"
    (step2 : |(d─g)| = |(a─c)| ∨ |(d─g)| = |(d─f)|) := by sorry

  euclid_apply (line_from_points e g) as EG
  euclid_apply (line_from_points f g) as FG
  euclid_sentence "1.24.3"
    "and let $EG$ and $FG$ have been joined. "
    (step3 : distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG) := by sorry

  -- @assumption_valid
  have step4_assumption1 : |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─g)| := by euclid_finish
  -- @assumption ("$AB$ is equal to $DE$ and $AC$ to $DG$", |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─g)|)
  euclid_sentence "1.24.4"
    "Therefore, since $AB$ is equal to $DE$ and $AC$ to $DG$, the two (straight-lines)  $BA$, $AC$ are equal to the two (straight-lines) $ED$, $DG$, respectively. "
    (step4 : |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)|) := by sorry

  euclid_sentence "1.24.5"
    "Also the angle $BAC$ is equal to the angle $EDG$."
    (step5 : ∠ b:a:c = ∠ e:d:g) := by sorry

  euclid_sentence "1.24.6"
    "Thus, the base $BC$ is equal  to the base $EG$ [Prop.~1.4]."
    (step6 : |(b─c)| = |(e─g)|) := by sorry

  -- @assumption_valid
  have step7_assumption1 : |(d─f)| = |(d─g)| := by linarith
  -- @assumption ("$DF$ is equal to $DG$", |(d─f)| = |(d─g)|)
  euclid_sentence "1.24.7"
    "Again, since $DF$ is equal to $DG$, angle $DGF$  is also equal to angle $DFG$ [Prop.~1.5]."
    (step7 : ∠ d:g:f = ∠ d:f:g) := by sorry

  euclid_sentence "1.24.8"
    "Thus, $DFG$ (is) greater than $EGF$. "
    (step8 : ∠ d:f:g > ∠ e:g:f) := by sorry

  euclid_sentence "1.24.9"
    "Thus, $EFG$ is much greater than $EGF$."
    (step9 : ∠ e:f:g > ∠ e:g:f) := by sorry

  -- @assumption_valid
  have step10_assumption1 : ∠ e:f:g > ∠ e:g:f := by assumption
  -- @assumption ("triangle $EFG$ has angle $EFG$  greater than $EGF$", ∠ e:f:g > ∠ e:g:f)
  euclid_sentence "1.24.10"
    "And since triangle $EFG$ has angle $EFG$  greater than $EGF$, and the greater angle is subtended by the greater side [Prop.~1.19], side $EG$ (is) thus also greater than $EF$."
    (step10 : |(e─g)| > |(e─f)|) := by sorry

  euclid_sentence "1.24.11"
    "But $EG$ (is) equal to  $BC$."
    (step11 : |(e─g)| = |(b─c)|) := by sorry

  euclid_sentence "1.24.12"
    "Thus, $BC$ (is) also greater than $EF$. "
    (step12 : |(b─c)| > |(e─f)|) := by sorry

  exact step12
  euclid_conclude_sentence "1.24.13"
    "Thus, if two triangles have two sides equal to two sides, respectively,  but (one) has the angle encompassed by the equal straight-lines greater than the   (corresponding) angle (in the other), then (the former triangle) will also have a base greater than the base (of the latter).  (Which is) the very thing it was required to show."

end Elements.Book1
