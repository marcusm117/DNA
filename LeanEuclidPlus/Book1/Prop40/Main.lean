import SystemE
import Book1.Prop31.Main
import Book1.Prop40.step1
import Book1.Prop40.step3
import Book1.Prop40.step4
import Book1.Prop40.step5
import Book1.Prop40.step6
import Book1.Prop40.step7
import Book1.Prop40.step8
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_40 : ∀  (a b c d e : Point) (AB BC AC CD DE AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d c e CD BC DE ∧ a.sameSide d BC ∧ b ≠ e ∧ |(b─c)| = |(c─e)| ∧
  distinctPointsOnLine a d AD ∧ (Triangle.area △ a:b:c = Triangle.area △ d:c:e) →
  ¬(AD.intersectsLine BC) := by
  euclid_intros
  euclid_intro_sentence "1.40.0"
    "Equal triangles which are on equal bases, and on the same side, are also between the same parallels.  Let $ABC$ and $CDE$ be equal triangles on the equal bases $BC$ and $CE$ (respectively), and on the same side (of $BE$). I say that they are also between the same parallels. "

  euclid_sentence "1.40.1"
    "For let $AD$ have been joined."
    (step1 : distinctPointsOnLine a d AD) := by euclid_apply (helper_1_40_step1 a d AD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)))

  -- BE is the same line as BC
  euclid_wts "1.40.2"
    "I say that $AD$ is parallel to $BE$. "

  -- Euclid argues by contradiction: `euclid_intros` has already assumed AD meets BC
  -- (AD is not parallel to BE) and left the goal `False`.
  euclid_apply (proposition_31 a b c BC) as AF
  euclid_apply (intersection_lines AF CD) as f
  euclid_sentence "1.40.3"
    "For if not, let $AF$ have been drawn through $A$ parallel to $BE$ [Prop.~1.31],"
    (step3 : a.onLine AF ∧ ¬(AF.intersectsLine BC)) := by euclid_apply (helper_1_40_step3 a AF BC (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine BC; assumption)))

  euclid_apply (line_from_points f e) as FE
  euclid_sentence "1.40.4"
    "and let $FE$ have been joined."
    (step4 : distinctPointsOnLine f e FE) := by euclid_apply (helper_1_40_step4 a d f e FE AF BC (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show a.sameSide d BC; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine BC; assumption)))

  -- @assumption_valid
  have step5_assumption1 : |(b─c)| = |(c─e)| := by assumption
  -- @assumption_valid
  have step5_assumption2 : ¬(AF.intersectsLine BC) := by assumption
  -- @assumption ("$BC$ and $CE$", |(b─c)| = |(c─e)|)
  -- @assumption ("$BE$ and $AF$", ¬(AF.intersectsLine BC))
  euclid_sentence "1.40.5"
    "Thus, triangle $ABC$ is equal to triangle $FCE$. For they are on equal bases, $BC$ and $CE$, and between the same parallels, $BE$ and $AF$ [Prop.~1.38]."
    (step5 : Triangle.area △ a:b:c = Triangle.area △ f:c:e) := by euclid_apply (helper_1_40_step5 a b c f e AB BC AC CD AF FE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show f.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show CD ≠ BC; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "$BC$ and $CE$" (show |(b─c)| = |(c─e)|; assumption)) (by euclid_assumption "$BE$ and $AF$" (show ¬(AF.intersectsLine BC); assumption)))

  euclid_sentence "1.40.6"
    "But, triangle $ABC$ is equal to [triangle] $DCE$."
    (step6 : Triangle.area △ a:b:c = Triangle.area △ d:c:e) := by euclid_apply (helper_1_40_step6 a b c d e (by euclid_assumption "" (show Triangle.area △ a:b:c = Triangle.area △ d:c:e; assumption)))

  euclid_sentence "1.40.7"
    "Thus, [triangle] $DCE$ is also equal to triangle $FCE$, the greater to the lesser."
    (step7 : Triangle.area △ d:c:e = Triangle.area △ f:c:e) := by euclid_apply (helper_1_40_step7 a b c d e f (by euclid_assumption "" (show Triangle.area △ a:b:c = Triangle.area △ f:c:e; assumption)) (by euclid_assumption "" (show Triangle.area △ a:b:c = Triangle.area △ d:c:e; assumption)))

  euclid_sentence "1.40.8"
    "The very thing is impossible. "
    (step8 : False) := by euclid_apply (helper_1_40_step8 a b c d e f BC AF CD AD DE FE (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show f.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine BC; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show AD.intersectsLine BC; assumption)) (by euclid_assumption "" (show CD ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ DE; assumption)) (by euclid_assumption "" (show DE ≠ CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "" (show |(b─c)| = |(c─e)|; assumption)) (by euclid_assumption "" (show a.sameSide d BC; assumption)) (by euclid_assumption "" (show Triangle.area △ d:c:e = Triangle.area △ f:c:e; assumption)))
  -- the following euclid sentences are redundant, and honestly a little silly logically speaking  since he has already proven the wts of "I say that $AD$ is parallel to $BE$. " with the previosu "impossible" by contradiction, so we are done.
  euclid_conclude_sentence "1.40.9"
    "Thus, $AF$ is not parallel to $BE$."
  euclid_conclude_sentence "1.40.10"
    "Similarly, we can show that neither (is) any other (straight-line) than $AD$."
  euclid_conclude_sentence "1.40.11"
    "Thus, $AD$ is parallel to $BE$. "
  exact step8
  euclid_conclude_sentence "1.40.12"
    "Thus, equal triangles which are on equal bases, and on the same side, are also between the same parallels. (Which is) the very thing it was required to show."

end Elements.Book1
