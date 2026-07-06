import SystemE
import Book1.Prop03.Main
import Book1Variants.Prop23
import Mathlib.Tactic.Linarith
import Book1.Prop24.step1
import Book1.Prop24.step2
import Book1.Prop24.step3
import Book1.Prop24.step4
import Book1.Prop24.step5
import Book1.Prop24.step6
import Book1.Prop24.step7
import Book1.Prop24.step8
import Book1.Prop24.step9
import Book1.Prop24.step10
import Book1.Prop24.step11
import Book1.Prop24.step12
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

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
    (step1 : ∠ e:d:g = ∠ b:a:c) := by euclid_apply (helper_1_24_step1 d e g g' g'' DE DG (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g'.onLine DG; assumption)) (by euclid_assumption "" (show g''.onLine DG; assumption)) (by euclid_assumption "" (show between d g' g''; assumption)) (by euclid_assumption "" (show between d g g''; assumption)) (by euclid_assumption "" (show g' ≠ d; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show ∠ g':d:e = ∠ b:a:c; assumption)) (by euclid_assumption "angle $BAC$ is greater than angle $EDF$" (show ∠ b:a:c > ∠ e:d:f; assumption)))

  euclid_sentence "1.24.2"
    "And let $DG$ be made equal to either of $AC$ or $DF$ [Prop.~1.3],"
    (step2 : |(d─g)| = |(a─c)| ∨ |(d─g)| = |(d─f)|) := by euclid_apply (helper_1_24_step2 d g a c (by euclid_assumption "" (show |(d─g)| = |(a─c)|; assumption)))

  euclid_apply (line_from_points e g) as EG
  euclid_apply (line_from_points f g) as FG
  euclid_sentence "1.24.3"
    "and let $EG$ and $FG$ have been joined. "
    (step3 : distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG) := by euclid_apply (helper_1_24_step3 d e g f DE EF DF DG EG FG (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show DE ≠ EF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g''.onLine DG; assumption)) (by euclid_assumption "" (show between d g g''; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show ∠ e:d:g = ∠ b:a:c; assumption)) (by euclid_assumption "" (show ∠ b:a:c > ∠ e:d:f; assumption)))

  -- @assumption_valid
  have step4_assumption1 : |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─g)| := by euclid_finish
  -- @assumption ("$AB$ is equal to $DE$ and $AC$ to $DG$", |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─g)|)
  euclid_sentence "1.24.4"
    "Therefore, since $AB$ is equal to $DE$ and $AC$ to $DG$, the two (straight-lines)  $BA$, $AC$ are equal to the two (straight-lines) $ED$, $DG$, respectively. "
    (step4 : |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)|) := by euclid_apply (helper_1_24_step4 (by euclid_assumption "$AB$ is equal to $DE$ and $AC$ to $DG$" (show |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─g)|; assumption)))

  euclid_sentence "1.24.5"
    "Also the angle $BAC$ is equal to the angle $EDG$."
    (step5 : ∠ b:a:c = ∠ e:d:g) := by euclid_apply (helper_1_24_step5 (by euclid_assumption "" (show ∠ e:d:g = ∠ b:a:c; assumption)))

  euclid_sentence "1.24.6"
    "Thus, the base $BC$ is equal  to the base $EG$ [Prop.~1.4]."
    (step6 : |(b─c)| = |(e─g)|) := by euclid_apply (helper_1_24_step6 a b c d e g g'' AB BC AC DE EG DG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g''.onLine DG; assumption)) (by euclid_assumption "" (show between d g g''; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by euclid_assumption "" (show |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∠ e:d:g; assumption)))

  -- @assumption_valid
  have step7_assumption1 : |(d─f)| = |(d─g)| := by linarith
  -- @assumption ("$DF$ is equal to $DG$", |(d─f)| = |(d─g)|)
  euclid_sentence "1.24.7"
    "Again, since $DF$ is equal to $DG$, angle $DGF$  is also equal to angle $DFG$ [Prop.~1.5]."
    (step7 : ∠ d:g:f = ∠ d:f:g) := by euclid_apply (helper_1_24_step7 a b c d e g f g' g'' AB BC AC DE EF DF DG EG FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g'.onLine DG; assumption)) (by euclid_assumption "" (show between d g' g''; assumption)) (by euclid_assumption "" (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by euclid_assumption "" (show ∠ g':d:e = ∠ b:a:c; assumption)) (by euclid_assumption "" (show g''.onLine DG; assumption)) (by euclid_assumption "" (show between d g g''; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by euclid_assumption "" (show |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)|; assumption)) (by euclid_assumption "" (show ∠ e:d:g = ∠ b:a:c; assumption)) (by euclid_assumption "" (show ∠ b:a:c > ∠ e:d:f; assumption)) (by euclid_assumption "$DF$ is equal to $DG$" (show |(d─f)| = |(d─g)|; assumption)))

  euclid_sentence "1.24.8"
    "Thus, $DFG$ (is) greater than $EGF$. "
    (step8 : ∠ d:f:g > ∠ e:g:f) := by euclid_apply (helper_1_24_step8 a b c d e f g g' g'' AB BC AC DE EF DF DG EG FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show DE ≠ EF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g'.onLine DG; assumption)) (by euclid_assumption "" (show between d g' g''; assumption)) (by euclid_assumption "" (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by euclid_assumption "" (show ∠ g':d:e = ∠ b:a:c; assumption)) (by euclid_assumption "" (show g''.onLine DG; assumption)) (by euclid_assumption "" (show between d g g''; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by euclid_assumption "" (show ∠ e:d:g = ∠ b:a:c; assumption)) (by euclid_assumption "" (show ∠ b:a:c > ∠ e:d:f; assumption)) (by euclid_assumption "" (show |(d─f)| = |(d─g)|; assumption)) (by euclid_assumption "" (show ∠ d:g:f = ∠ d:f:g; assumption)))

  euclid_sentence "1.24.9"
    "Thus, $EFG$ is much greater than $EGF$."
    (step9 : ∠ e:f:g > ∠ e:g:f) := by euclid_apply (helper_1_24_step9 a b c d e f g g' g'' AB BC AC DE EF DF DG EG FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show DE ≠ EF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g'.onLine DG; assumption)) (by euclid_assumption "" (show between d g' g''; assumption)) (by euclid_assumption "" (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by euclid_assumption "" (show ∠ g':d:e = ∠ b:a:c; assumption)) (by euclid_assumption "" (show g''.onLine DG; assumption)) (by euclid_assumption "" (show between d g g''; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by euclid_assumption "" (show ∠ e:d:g = ∠ b:a:c; assumption)) (by euclid_assumption "" (show ∠ b:a:c > ∠ e:d:f; assumption)) (by euclid_assumption "" (show |(d─f)| = |(d─g)|; assumption)) (by euclid_assumption "" (show ∠ d:g:f = ∠ d:f:g; assumption)) (by euclid_assumption "" (show ∠ d:f:g > ∠ e:g:f; assumption)))

  -- @assumption_valid
  have step10_assumption1 : ∠ e:f:g > ∠ e:g:f := by assumption
  -- @assumption ("triangle $EFG$ has angle $EFG$  greater than $EGF$", ∠ e:f:g > ∠ e:g:f)
  euclid_sentence "1.24.10"
    "And since triangle $EFG$ has angle $EFG$  greater than $EGF$, and the greater angle is subtended by the greater side [Prop.~1.19], side $EG$ (is) thus also greater than $EF$."
    (step10 : |(e─g)| > |(e─f)|) := by euclid_apply (helper_1_24_step10 a b c d e f g g' g'' AB BC AC DE EF DF DG EG FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show DE ≠ EF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g'.onLine DG; assumption)) (by euclid_assumption "" (show between d g' g''; assumption)) (by euclid_assumption "" (show g'.onLine DE ∨ g'.sameSide f DE; assumption)) (by euclid_assumption "" (show ∠ g':d:e = ∠ b:a:c; assumption)) (by euclid_assumption "" (show g''.onLine DG; assumption)) (by euclid_assumption "" (show between d g g''; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e g EG ∧ distinctPointsOnLine f g FG; assumption)) (by euclid_assumption "" (show ∠ e:d:g = ∠ b:a:c; assumption)) (by euclid_assumption "" (show ∠ b:a:c > ∠ e:d:f; assumption)) (by euclid_assumption "triangle $EFG$ has angle $EFG$  greater than $EGF$" (show ∠ e:f:g > ∠ e:g:f; assumption)))

  euclid_sentence "1.24.11"
    "But $EG$ (is) equal to  $BC$."
    (step11 : |(e─g)| = |(b─c)|) := by euclid_apply (helper_1_24_step11 b c e g (by euclid_assumption "" (show |(b─c)| = |(e─g)|; assumption)))

  euclid_sentence "1.24.12"
    "Thus, $BC$ (is) also greater than $EF$. "
    (step12 : |(b─c)| > |(e─f)|) := by euclid_apply (helper_1_24_step12 b c e f g (by euclid_assumption "" (show |(e─g)| > |(e─f)|; assumption)) (by euclid_assumption "" (show |(e─g)| = |(b─c)|; assumption)))

  exact step12
  euclid_conclude_sentence "1.24.13"
    "Thus, if two triangles have two sides equal to two sides, respectively,  but (one) has the angle encompassed by the equal straight-lines greater than the   (corresponding) angle (in the other), then (the former triangle) will also have a base greater than the base (of the latter).  (Which is) the very thing it was required to show."

end Elements.Book1
