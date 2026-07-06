import SystemE
import Book1.Prop01.variants
import Book1.Prop03.Main
import Mathlib.Tactic.Linarith
import Book1.Prop11.step1
import Book1.Prop11.step2
import Book1.Prop11.step3
import Book1.Prop11.step4
import Book1.Prop11.step6
import Book1.Prop11.step7
import Book1.Prop11.step8
import Book1.Prop11.step9
import Book1.Prop11.step10
import Book1.Prop11.step11
import Book1.Prop11.hfAB
import Book1.Prop11.hperp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
-- map done
theorem proposition_11 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  exists f : Point, ¬(f.onLine AB) ∧ (∠ a:c:f = ∟) := by
  euclid_intros
  euclid_intro_sentence "1.11.0"
    "To draw a straight-line at right-angles to a given straight-line from a given point on it.  Let $AB$ be the given straight-line, and $C$ the given point on it. So it is required to draw a straight-line from the point $C$ at right-angles to the straight-line $AB$. "

  euclid_apply (point_between_points_shorter_than AB c a (c─b)) as d
  euclid_sentence "1.11.1"
    "Let the point $D$ be have been taken at random on $AC$,"
    (step1 : between a d c) := by euclid_apply (helper_1_11_step1 a c d (by euclid_assumption "" (show between c d a; assumption)))

  euclid_apply (proposition_3 c b c d AB AB) as e
  euclid_sentence "1.11.2"
    "and let $CE$ be made equal to $CD$ [Prop.~1.3],"
    (step2 : |(c─e)| = |(c─d)|) := by euclid_apply (helper_1_11_step2 c d e (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)))

  euclid_apply (proposition_1 d e AB) as f
  euclid_apply (line_from_points d f) as DF
  euclid_apply (line_from_points f e) as FE
  euclid_sentence "1.11.3"
    "and let the equilateral triangle $FDE$ have been constructed on $DE$ [Prop.~1.1],"
    (step3 : formTriangle f d e DF AB FE ∧ |(f─d)| = |(d─e)| ∧ |(f─e)| = |(d─e)|) := by euclid_apply (helper_1_11_step3 a b c d e f AB DF FE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show between c e b; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)))

  euclid_apply (line_from_points f c) as FC
  euclid_sentence "1.11.4"
    "and let $FC$ have been joined."
    (step4 : distinctPointsOnLine f c FC) := by euclid_apply (helper_1_11_step4 a b c d e f AB FC (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show between c e b; assumption)) (by euclid_assumption "" (show |(c─d)| < |(c─b)|; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)))

  euclid_wts "1.11.5"
    "I say that the straight-line $FC$ has been drawn at right-angles to the given straight-line $AB$ from the given point $C$ on it. "

  -- @assumption_valid
  have step6_assumption1 : |(c─d)| = |(c─e)| := by linarith
  -- @assumption_valid
  have step6_assumption2 : |(c─f)| = |(c─f)| := by rfl
  -- @assumption ("$DC$ is equal to $CE$", |(c─d)| = |(c─e)|)
  -- @assumption ("$CF$ is common", |(c─f)| = |(c─f)|)
  euclid_sentence "1.11.6"
    "For since $DC$ is equal to $CE$, and $CF$ is common, the two (straight-lines) $DC$, $CF$ are equal to the two (straight-lines), $EC$, $CF$, respectively. "
    (step6 : |(c─d)| = |(c─e)| ∧ |(c─f)| = |(c─f)|) := by euclid_apply (helper_1_11_step6 (by euclid_assumption "$DC$ is equal to $CE$" (show |(c─d)| = |(c─e)|; assumption)) (by euclid_assumption "$CF$ is common" (show |(c─f)| = |(c─f)|; assumption)))

  euclid_sentence "1.11.7"
    "And the base $DF$ is equal to the base $FE$."
    (step7 : |(d─f)| = |(f─e)|) := by euclid_apply (helper_1_11_step7 d e f (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)))

  euclid_sentence "1.11.8"
    "Thus, the angle $DCF$ is equal to the angle $ECF$ [Prop.~1.8],"
    (step8 : ∠ d:c:f = ∠ e:c:f) := by euclid_apply (helper_1_11_step8 a b c d e f AB DF FE FC (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show between c e b; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show DF ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ FE; assumption)) (by euclid_assumption "" (show FE ≠ DF; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─e)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(f─e)|; assumption)))

  euclid_sentence "1.11.9"
    "and they are adjacent."
    (step9 : between d c e) := by euclid_apply (helper_1_11_step9 a b c d e AB (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show between c e b; assumption)))

  -- @assumption_valid
  have step10_assumption1 : ∠ d:c:f = ∠ e:c:f ∧ between d c e := by euclid_finish
  -- @assumption ("a straight-line stood on  a(nother) straight-line makes the adjacent angles equal to one another", ∠ d:c:f = ∠ e:c:f ∧ between d c e)
  euclid_sentence "1.11.10"
    "But when a straight-line stood on  a(nother) straight-line makes the adjacent angles equal to one another, each of the equal angles is a right-angle [Def.~1.10]."
    (step10 : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟) := by euclid_apply (helper_1_11_step10 a b c d e f AB (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show between c e b; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)) (by euclid_assumption "a straight-line stood on  a(nother) straight-line makes the adjacent angles equal to one another" (show ∠ d:c:f = ∠ e:c:f ∧ between d c e; assumption)))

  euclid_sentence "1.11.11"
    "Thus, each of the (angles) $DCF$ and $FCE$ is a right-angle. "
    (step11 : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟) := by euclid_apply (helper_1_11_step11 (by euclid_assumption "" (show ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟; assumption)))

  use f
  have hfAB : ¬(f.onLine AB) := by euclid_apply (helper_1_11_hfAB a b c d e f AB (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show between c e b; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)))
  have hperp : ∠ a:c:f = ∟ := by euclid_apply (helper_1_11_hperp a b c d e f AB FC (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬(f.onLine AB); assumption)) (by euclid_assumption "" (show ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟; assumption)))
  exact ⟨hfAB, hperp⟩
  euclid_conclude_sentence "1.11.12"
    "Thus, the straight-line $CF$ has been drawn at right-angles to the given straight-line $AB$ from the given point $C$ on it. (Which is) the very thing it was required to do."

end Elements.Book1
