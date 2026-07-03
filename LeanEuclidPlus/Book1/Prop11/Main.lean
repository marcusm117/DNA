import SystemE
import Book.Prop01
import Book.Prop03
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
-- map done
set_option systemE.solverTime 30 in
theorem proposition_11 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  exists f : Point, ¬(f.onLine AB) ∧ (∠ a:c:f = ∟) := by
  euclid_intros
  euclid_intro_sentence "1.11.0"
    "To draw a straight-line at right-angles to a given straight-line from a given point on it.  Let $AB$ be the given straight-line, and $C$ the given point on it. So it is required to draw a straight-line from the point $C$ at right-angles to the straight-line $AB$. "

  euclid_apply (point_between_points_shorter_than AB c a (c─b)) as d
  euclid_sentence "1.11.1"
    "Let the point $D$ be have been taken at random on $AC$,"
    (step1 : between a d c) := by sorry

  euclid_apply (proposition_3 c b c d AB AB) as e
  euclid_sentence "1.11.2"
    "and let $CE$ be made equal to $CD$ [Prop.~1.3],"
    (step2 : |(c─e)| = |(c─d)|) := by sorry

  euclid_apply (proposition_1 d e AB) as f
  euclid_apply (line_from_points d f) as DF
  euclid_apply (line_from_points f e) as FE
  euclid_sentence "1.11.3"
    "and let the equilateral triangle $FDE$ have been constructed on $DE$ [Prop.~1.1],"
    (step3 : formTriangle f d e DF AB FE ∧ |(f─d)| = |(d─e)| ∧ |(f─e)| = |(d─e)|) := by sorry

  euclid_apply (line_from_points f c) as FC
  euclid_sentence "1.11.4"
    "and let $FC$ have been joined."
    (step4 : distinctPointsOnLine f c FC) := by sorry

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
    (step6 : |(c─d)| = |(c─e)| ∧ |(c─f)| = |(c─f)|) := by sorry

  euclid_sentence "1.11.7"
    "And the base $DF$ is equal to the base $FE$."
    (step7 : |(d─f)| = |(f─e)|) := by sorry

  euclid_sentence "1.11.8"
    "Thus, the angle $DCF$ is equal to the angle $ECF$ [Prop.~1.8],"
    (step8 : ∠ d:c:f = ∠ e:c:f) := by sorry

  euclid_sentence "1.11.9"
    "and they are adjacent."
    (step9 : between d c e) := by sorry

  -- @assumption_valid
  have step10_assumption1 : ∠ d:c:f = ∠ e:c:f ∧ between d c e := by euclid_finish
  -- @assumption ("a straight-line stood on  a(nother) straight-line makes the adjacent angles equal to one another", ∠ d:c:f = ∠ e:c:f ∧ between d c e)
  euclid_sentence "1.11.10"
    "But when a straight-line stood on  a(nother) straight-line makes the adjacent angles equal to one another, each of the equal angles is a right-angle [Def.~1.10]."
    (step10 : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟) := by sorry

  euclid_sentence "1.11.11"
    "Thus, each of the (angles) $DCF$ and $FCE$ is a right-angle. "
    (step11 : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟) := by sorry

  use f
  have hfAB : ¬(f.onLine AB) := by sorry
  have hperp : ∠ a:c:f = ∟ := by sorry
  exact ⟨hfAB, hperp⟩
  euclid_conclude_sentence "1.11.12"
    "Thus, the straight-line $CF$ has been drawn at right-angles to the given straight-line $AB$ from the given point $C$ on it. (Which is) the very thing it was required to do."

end Elements.Book1
