import SystemE
import Book1.Prop01.step1
import Book1.Prop01.step2
import Book1.Prop01.step3
import Book1.Prop01.step4
import Book1.Prop01.step5
import Book1.Prop01.step6
import Book1.Prop01.step7
import Book1.Prop01.step8
import Book1.Prop01.step9
import Book1.Prop01.step10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_1 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| := by
  euclid_intros
  euclid_intro_sentence "1.1.0"
    "To construct an equilateral triangle on a given finite straight-line. Let $AB$ be the given finite straight-line. So it is required to construct an equilateral triangle on the straight-line $AB$."

  euclid_apply (circle_from_points a b) as BCD
  euclid_sentence "1.1.1"
    "Let the circle $BCD$ with center $A$ and radius $AB$ have been drawn [Post.~3],"
    (step1 : a.isCentre BCD ∧ b.onCircle BCD) := by euclid_apply (helper_1_1_step1 a b BCD (by euclid_assumption "" (show a.isCentre BCD; assumption)) (by euclid_assumption "" (show b.onCircle BCD; assumption)))

  -- note that the weird "And" is an artifact that the original text says "[Post.~].And" with no space.
  euclid_apply (circle_from_points b a) as ACE
  euclid_sentence "1.1.2"
    "and again let the circle $ACE$ with center $B$ and radius $BA$ have been drawn [Post.~3].And"
    (step2 : b.isCentre ACE ∧ a.onCircle ACE) := by euclid_apply (helper_1_1_step2 a b ACE (by euclid_assumption "" (show b.isCentre ACE; assumption)) (by euclid_assumption "" (show a.onCircle ACE; assumption)))

  euclid_apply (intersection_circles BCD ACE) as c
  euclid_apply (line_from_points c a) as CA
  euclid_apply (line_from_points c b) as CB
  euclid_sentence "1.1.3"
    "let the straight-lines $CA$ and $CB$ have been joined from the point $C$, where the circles cut one another, to the points $A$ and $B$ (respectively) [Post.~1].And"
    (step3 : distinctPointsOnLine c a CA ∧ distinctPointsOnLine c b CB) := by euclid_apply (helper_1_1_step3 a b c CA CB BCD ACE (by euclid_assumption "" (show c.onLine CA; assumption)) (by euclid_assumption "" (show a.onLine CA; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show a.isCentre BCD; assumption)) (by euclid_assumption "" (show c.onCircle BCD; assumption)) (by euclid_assumption "" (show b.isCentre ACE; assumption)) (by euclid_assumption "" (show c.onCircle ACE; assumption)))

  -- @assumption_valid
  have step4_assumption1 : a.isCentre BCD := by assumption
  -- @assumption ("the point $A$ is the center of the circle $CDB$", a.isCentre BCD)
  euclid_sentence "1.1.4"
    "since the point $A$ is the center of the circle $CDB$, $AC$ is equal to $AB$ [Def.~1.15]."
    (step4 : |(a─c)| = |(a─b)|) := by euclid_apply (helper_1_1_step4 a b c BCD (by euclid_assumption "the point $A$ is the center of the circle $CDB$" (show a.isCentre BCD; assumption)) (by euclid_assumption "" (show b.onCircle BCD; assumption)) (by euclid_assumption "" (show c.onCircle BCD; assumption)))

  -- @assumption_valid
  have step5_assumption1 : b.isCentre ACE := by assumption
  -- @assumption ("the point $B$ is the center of the circle $CAE$", b.isCentre ACE)
  euclid_sentence "1.1.5"
    "Again,since the point $B$ is the center of the circle $CAE$, $BC$ is equal to $BA$ [Def.~1.15]."
    (step5 : |(b─c)| = |(b─a)|) := by euclid_apply (helper_1_1_step5 a b c ACE (by euclid_assumption "the point $B$ is the center of the circle $CAE$" (show b.isCentre ACE; assumption)) (by euclid_assumption "" (show a.onCircle ACE; assumption)) (by euclid_assumption "" (show c.onCircle ACE; assumption)))

  euclid_sentence "1.1.6"
    "But $CA$ was also shown (to be) equal to $AB$."
    (step6 : |(c─a)| = |(a─b)|) := by euclid_apply (helper_1_1_step6 a b c (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)))

  euclid_sentence "1.1.7"
    "Thus, $CA$ and $CB$ are each equal to $AB$."
    (step7 : |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|) := by euclid_apply (helper_1_1_step7 a b c (by euclid_assumption "" (show |(c─a)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(b─c)| = |(b─a)|; assumption)))

  euclid_sentence "1.1.8"
    "But things equal to the same thing are also equal to one another [C.N.~1]."
    (step8 : (|(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|) → |(c─a)| = |(c─b)|) := by euclid_apply (helper_1_1_step8 a b c)

  euclid_sentence "1.1.9"
    "Thus, $CA$ is also equal to $CB$."
    (step9 : |(c─a)| = |(c─b)|) := by euclid_apply (helper_1_1_step9 a b c (by euclid_assumption "" (show |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|; assumption)) (by euclid_assumption "" (show (|(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|) → |(c─a)| = |(c─b)|; assumption)))

  euclid_sentence "1.1.10"
    "Thus, the three (straight-lines) $CA$, $AB$, and $BC$ are equal to one another.Thus,"
    (step10 : |(c─a)| = |(a─b)| ∧ |(a─b)| = |(b─c)|) := by euclid_apply (helper_1_1_step10 a b c (by euclid_assumption "" (show |(c─a)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(b─c)| = |(b─a)|; assumption)))

  exact ⟨c, step7⟩
  euclid_conclude_sentence "1.1.11"
    "the triangle $ABC$ is equilateral, and has been constructed on the given finite straight-line $AB$. (Which is) the very thing it was required to do."

end Elements.Book1
