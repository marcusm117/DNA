import SystemE
import Book1Variants.Prop23
import Book1.Prop27.Main
import Book1.Prop31.step1
import Book1.Prop31.step2
import Book1.Prop31.step3
import Book1.Prop31.step4
import Book1.Prop31.step5
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_31 : ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC ∧ ¬(a.onLine BC) →
  ∃ EF : Line, a.onLine EF ∧ ¬(EF.intersectsLine BC) := by
  euclid_intros
  euclid_intro_sentence "1.31.0"
    "To draw a straight-line parallel to a given straight-line, through a given point.  Let $A$ be the given point, and $BC$ the given straight-line. So it is required to draw a straight-line parallel to the straight-line $BC$, through the point $A$. "

  euclid_apply (exists_point_between_points_on_line BC b c) as d
  euclid_sentence "1.31.1"
    "Let the point $D$ have been taken a random  on $BC$,"
    (step1 : d.onLine BC) := by euclid_apply (helper_1_31_step1 d BC (by euclid_assumption "" (show d.onLine BC; assumption)))

  euclid_apply (line_from_points a d) as AD
  euclid_sentence "1.31.2"
    "and let $AD$ have been joined."
    (step2 : distinctPointsOnLine a d AD) := by euclid_apply (helper_1_31_step2 a d BC AD (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)))

  euclid_apply (proposition_23' a d d a c b AD AD BC) as e
  euclid_sentence "1.31.3"
    "And let (angle) $DAE$, equal to angle $ADC$,  have been constructed  on the straight-line $DA$ at the point $A$ on it [Prop.~1.23]."
    (step3 : ∠ d:a:e = ∠ a:d:c) := by euclid_apply (helper_1_31_step3 a d e c AD BC (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show ∠ e:a:d = ∠ a:d:c; assumption)))

  euclid_apply (line_from_points e a) as EF
  euclid_apply (extend_point EF e a) as f
  euclid_sentence "1.31.4"
    "And let the straight-line $AF$ have been produced in a straight-line with $EA$.  "
    (step4 : between e a f) := by euclid_apply (helper_1_31_step4 e a f (by euclid_assumption "" (show between e a f; assumption)))

  -- @assumption_valid
  have step5_assumption1 : ∠ e:a:d = ∠ a:d:c := by assumption
  -- @assumption ("the straight-line $AD$, (in) falling across the two straight-lines $BC$ and $EF$,  has made the alternate angles $EAD$ and $ADC$ equal to one another", ∠ e:a:d = ∠ a:d:c)
  euclid_sentence "1.31.5"
    "And since the straight-line $AD$, (in) falling across the two straight-lines $BC$ and $EF$,  has made the alternate angles $EAD$ and $ADC$ equal to one another, $EAF$ is thus parallel to $BC$ [Prop.~1.27]. "
    (step5 : ¬(EF.intersectsLine BC)) := by euclid_apply (helper_1_31_step5 a b c d e EF BC AD (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show a.onLine EF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show between b d c; assumption)) (by euclid_assumption "" (show e.onLine AD ∨ e.sameSide b AD; assumption)) (by euclid_assumption "the straight-line $AD$, (in) falling across the two straight-lines $BC$ and $EF$,  has made the alternate angles $EAD$ and $ADC$ equal to one another" (show ∠ e:a:d = ∠ a:d:c; assumption)))

  use EF
  euclid_conclude_sentence "1.31.6"
    "Thus, the straight-line $EAF$ has been drawn parallel to the given straight-line $BC$, through the  given point $A$. (Which is) the very thing it was required to do."

end Elements.Book1
