import SystemE
import Book1.Prop12.Main
import Mathlib.Tactic.Linarith
import Book3.Prop18.step1
import Book3.Prop18.step2
import Book3.Prop18.step3
import Book3.Prop18.step4
import Book3.Prop18.step5
import Book3.Prop18.step6
import Book3.Prop18.step7
import Book3.Prop18.step8
import Book3.Prop18.step9
import Book3.Prop18.hcdDE
import Book3.Prop18.hfoff
import Book3.Prop18.hb
open Elements.Book1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_18 : ∀ (c f : Point) (ABC : Circle) (DE : Line),
  c.onCircle ABC ∧ c.onLine DE ∧ ¬ DE.intersectsCircle ABC ∧
  f.isCentre ABC ∧ f ≠ c →
  ∀ d : Point, d.onLine DE → d ≠ c → ∠ f:c:d = ∟ :=
by
  euclid_intros
  euclid_intro_sentence "3.18.0"
    "If some straight-line touches a circle, and some (other) straight-line is joined from the center (of the circle) to the point of contact, (then) the (straight-line) so joined will be perpendicular to the tangent. For let some straight-line $DE$ touch the circle $ABC$ at point $C$, and let the center $F$ of circle $ABC$ be found [Prop.~3.1], and let $FC$ be joined from $F$ to $C$. I say that $FC$ is perpendicular to $DE$."

  have habsurd1 : ¬(∠ f:c:d ≠ ∟) := by
    intro hsuppose1
    have hcdDE : distinctPointsOnLine c d DE := by euclid_apply (helper_3_18_hcdDE c d DE (by euclid_assumption "" (show c.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)))
    have hfoff : ¬f.onLine DE := by euclid_apply (helper_3_18_hfoff f ABC DE (by euclid_assumption "" (show ¬DE.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)))
    euclid_apply (proposition_12 c d f DE) as g
    euclid_apply (line_from_points f g) as FG
    euclid_sentence "3.18.1"
      "For if not, let $FG$ be drawn from $F$, perpendicular to $DE$ [Prop.~1.12]."
      (step1 : g.onLine DE ∧ f.onLine FG ∧ g.onLine FG ∧ (∠ c:g:f = ∟ ∨ ∠ d:g:f = ∟)) := by euclid_apply (helper_3_18_step1 c d f g DE FG (by euclid_assumption "" (show g.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show ∠ c:g:f = ∟ ∨ ∠ d:g:f = ∟; assumption)))

    -- @assumption_valid
    have step2_assumption1 : ∠ f:g:c = ∟ := by euclid_finish
    -- @assumption ("angle $FGC$ is a right-angle", ∠ f:g:c = ∟)
    euclid_sentence "3.18.2"
      "Therefore, since angle $FGC$ is a right-angle, (angle) $FCG$ is thus acute [Prop.~1.17]."
      (step2 : ∠ f:c:g < ∟) := by euclid_apply (helper_3_18_step2 c f g d DE FG (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine DE; assumption)) (by euclid_assumption "" (show ¬f.onLine DE; assumption)) (by euclid_assumption "" (show f ≠ c; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show ∠ f:c:d ≠ ∟; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine DE → p ≠ g → ∠ p:g:f = ∟; assumption)) (by euclid_assumption "angle $FGC$ is a right-angle" (show ∠ f:g:c = ∟; assumption)))

    -- @assumption_valid
    have step3_assumption1 : ∠ f:g:c > ∠ f:c:g := by linarith
    -- @assumption ("the greater angle is subtended by the greater side [Prop.~1.19]", ∠ f:g:c > ∠ f:c:g)
    euclid_sentence "3.18.3"
      "And the greater angle is subtended by the greater side [Prop.~1.19]. Thus, $FC$ (is) greater than $FG$."
      (step3 : |(f─c)| > |(f─g)|) := by euclid_apply (helper_3_18_step3 c f g DE FG (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine DE; assumption)) (by euclid_assumption "" (show ¬f.onLine DE; assumption)) (by euclid_assumption "" (show f ≠ c; assumption)) (by euclid_assumption "the greater angle is subtended by the greater side [Prop.~1.19]" (show ∠ f:g:c > ∠ f:c:g; assumption)))

    have hb : ∃ b : Point, b.onCircle ABC ∧ b ≠ c := by euclid_apply (helper_3_18_hb ABC c)
    obtain ⟨b, hbcircle, hbc⟩ := hb
    euclid_sentence "3.18.4"
      "And $FC$ (is) equal to $FB$."
      (step4 : |(f─c)| = |(f─b)|) := by euclid_apply (helper_3_18_step4 f c b ABC (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)))

    euclid_sentence "3.18.5"
      "Thus, $FB$ (is) also greater than $FG$, the lesser than the greater."
      (step5 : |(f─b)| > |(f─g)|) := by euclid_apply (helper_3_18_step5 f c b g (by euclid_assumption "" (show |(f─c)| > |(f─g)|; assumption)) (by euclid_assumption "" (show |(f─c)| = |(f─b)|; assumption)))

    euclid_sentence "3.18.6"
      "The very thing is impossible."
      (step6 : False) := by euclid_apply (helper_3_18_step6 f b g ABC DE (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onLine DE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show |(f─b)| > |(f─g)|; assumption)))
    exact step6

  euclid_sentence "3.18.7"
    "Thus, $FG$ is not perpendicular to $DE$."
    (step7 : ¬(∠ f:c:d ≠ ∟)) := by euclid_apply (helper_3_18_step7 c d f (by euclid_assumption "" (show ¬(∠ f:c:d ≠ ∟); assumption)))

  euclid_sentence "3.18.8"
    "So, similarly, we can show that neither (is) any other (straight-line) except $FC$."
    (step8 : ∀ (g' : Point),
      g'.onLine DE → g' ≠ c →
      ¬∠ c:g':f = ∟) := by euclid_apply (helper_3_18_step8 c f ABC DE (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onLine DE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show f ≠ c; assumption)))

  euclid_sentence "3.18.9"
    "Thus, $FC$ is perpendicular to $DE$."
    (step9 : ∠ f:c:d = ∟) := by euclid_apply (helper_3_18_step9 c f d (by euclid_assumption "" (show ¬(∠ f:c:d ≠ ∟); assumption)))

  exact step9
  euclid_conclude_sentence "3.18.10"
    "Thus, if some straight-line touches a circle, and some (other) straight-line is joined from the center (of the circle) to the point of contact, (then) the (straight-line) so joined will be perpendicular to the tangent. (Which is) the very thing it was required to show."

end Elements.Book3
