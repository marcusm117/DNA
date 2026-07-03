import SystemE
import Book.Prop01
import Book1.Prop02.step1
import Book1.Prop02.step2
import Book1.Prop02.step3
import Book1.Prop02.step4
import Book1.Prop02.step5
import Book1.Prop02.step6
import Book1.Prop02.step7
import Book1.Prop02.step8
import Book1.Prop02.step9
import Book1.Prop02.step10
import Book1.Prop02.step11
import Book1.Prop02.step12
import Book1.Prop02.step13
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_2 : ∀ (a b c : Point) (BC : Line),
  (distinctPointsOnLine b c BC) ∧ (a ≠ b) →
  ∃ l : Point, |(a─l)| = |(b─c)| := by
  euclid_intros
  euclid_intro_sentence "1.2.0"
    "To place a straight-line equal to a given straight-line at a given point (as an extremity). Let $A$ be the given point, and $BC$ the given straight-line. So  it is required to place a straight-line at point $A$ equal to the given straight-line $BC$. "

  euclid_apply (line_from_points a b) as AB
  euclid_sentence "1.2.1"
    "For  let the straight-line $AB$ have been joined from point $A$ to point $B$ [Post.~1],"
    (step1 : distinctPointsOnLine a b AB) := by euclid_apply (helper_1_2_step1 a b AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))

  euclid_apply (proposition_1 a b AB) as d
  euclid_apply (line_from_points d a) as DA
  euclid_apply (line_from_points d b) as DB
  euclid_sentence "1.2.2"
    "and let the equilateral triangle $DAB$ have been been constructed upon it [Prop.~1.1]. "
    (step2 : formTriangle d a b DA AB DB ∧ |(d─a)| = |(a─b)| ∧ |(d─b)| = |(a─b)|) := by euclid_apply (helper_1_2_step2 d a b DA AB DB (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show |(d─a)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(d─b)| = |(a─b)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))

  euclid_apply (extend_point DA d a) as e
  euclid_apply (extend_point DB d b) as f
  euclid_sentence "1.2.3"
    "And let the straight-lines $AE$ and $BF$ have been produced in a straight-line with $DA$ and $DB$  (respectively) [Post.~2]."
    (step3 : between d a e ∧ between d b f) := by euclid_apply (helper_1_2_step3 d a b e f (by euclid_assumption "" (show between d a e; assumption)) (by euclid_assumption "" (show between d b f; assumption)))

  euclid_apply (circle_from_points b c) as CGH
  euclid_sentence "1.2.4"
    "And let the circle $CGH$ with center $B$ and radius $BC$ have been drawn [Post.~3],"
    (step4 : b.isCentre CGH ∧ c.onCircle CGH) := by euclid_apply (helper_1_2_step4 b c CGH (by euclid_assumption "" (show b.isCentre CGH; assumption)) (by euclid_assumption "" (show c.onCircle CGH; assumption)))

  euclid_apply (intersection_circle_line_extending_points CGH DB b d) as g
  euclid_apply (circle_from_points d g) as GKL
  euclid_sentence "1.2.5"
    "and again let the circle $GKL$ with center $D$ and radius $DG$ have been drawn [Post.~3].     "
    (step5 : d.isCentre GKL ∧ g.onCircle GKL) := by euclid_apply (helper_1_2_step5 d g GKL (by euclid_assumption "" (show d.isCentre GKL; assumption)) (by euclid_assumption "" (show g.onCircle GKL; assumption)))

  euclid_apply (intersection_circle_line_extending_points GKL DA a d) as l
  -- @assumption_valid
  have step6_assumption1 : b.isCentre CGH := by assumption
  -- @assumption ("the point $B$ is the center of (the circle) $CGH$", b.isCentre CGH)
  euclid_sentence "1.2.6"
    "Therefore, since the point $B$ is the center of (the circle) $CGH$, $BC$ is equal to  $BG$ [Def.~1.15]."
    (step6 : |(b─c)| = |(b─g)|) := by euclid_apply (helper_1_2_step6 b c g CGH (by euclid_assumption "the point $B$ is the center of (the circle) $CGH$" (show b.isCentre CGH; assumption)) (by euclid_assumption "" (show c.onCircle CGH; assumption)) (by euclid_assumption "" (show g.onCircle CGH; assumption)))

  -- @assumption_valid
  have step7_assumption1 : d.isCentre GKL := by assumption
  -- @assumption ("the point $D$ is the center of the circle $GKL$", d.isCentre GKL)
  euclid_sentence "1.2.7"
    "Again, since the point $D$ is the center of the circle $GKL$, $DL$ is equal to $DG$ [Def.~1.15]."
    (step7 : |(d─l)| = |(d─g)|) := by euclid_apply (helper_1_2_step7 d l g GKL (by euclid_assumption "the point $D$ is the center of the circle $GKL$" (show d.isCentre GKL; assumption)) (by euclid_assumption "" (show l.onCircle GKL; assumption)) (by euclid_assumption "" (show g.onCircle GKL; assumption)))

  euclid_sentence "1.2.8"
    "And within these,  $DA$ is equal to $DB$."
    (step8 : |(d─a)| = |(d─b)|) := by euclid_apply (helper_1_2_step8 d a b (by euclid_assumption "" (show |(d─a)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(d─b)| = |(a─b)|; assumption)))

  euclid_sentence "1.2.9"
    "Thus, the remainder $AL$ is equal to the remainder $BG$ [C.N.~3]."
    (step9 : |(a─l)| = |(b─g)|) := by euclid_apply (helper_1_2_step9 d a b g l (by euclid_assumption "" (show |(d─l)| = |(d─g)|; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)) (by euclid_assumption "" (show between l a d; assumption)) (by euclid_assumption "" (show between g b d; assumption)))

  euclid_sentence "1.2.10"
    "But $BC$ was also shown (to be)  equal to $BG$."
    (step10 : |(b─c)| = |(b─g)|) := by euclid_apply (helper_1_2_step10 b c g (by euclid_assumption "" (show |(b─c)| = |(b─g)|; assumption)))

  euclid_sentence "1.2.11"
    "Thus,  $AL$ and $BC$ are each equal to $BG$."
    (step11 : |(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)|) := by euclid_apply (helper_1_2_step11 a l b c g (by euclid_assumption "" (show |(a─l)| = |(b─g)|; assumption)) (by euclid_assumption "" (show |(b─c)| = |(b─g)|; assumption)))

  euclid_sentence "1.2.12"
    "But things equal to the same thing are also equal to one another [C.N.~1]."
    (step12 : (|(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)|) → |(a─l)| = |(b─c)|) := by euclid_apply (helper_1_2_step12 a l b c g)

  euclid_sentence "1.2.13"
    "Thus, $AL$ is also equal to $BC$. "
    (step13 : |(a─l)| = |(b─c)|) := by euclid_apply (helper_1_2_step13 a l b c g (by euclid_assumption "" (show |(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)|; assumption)) (by euclid_assumption "" (show (|(a─l)| = |(b─g)| ∧ |(b─c)| = |(b─g)|) → |(a─l)| = |(b─c)|; assumption)))

  exact ⟨l, step13⟩
  euclid_conclude_sentence "1.2.14"
    "Thus, the straight-line $AL$, equal to the given straight-line $BC$, has been placed at the given point $A$. (Which is) the very thing it was required to do."

end Elements.Book1
