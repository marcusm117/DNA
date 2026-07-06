import SystemE
import Book1.Prop01.variants
import Book1.Prop03.Main
import Mathlib.Tactic.Linarith
import Book1.Prop09.step1
import Book1.Prop09.step2
import Book1.Prop09.step3
import Book1.Prop09.step4
import Book1.Prop09.step5
import Book1.Prop09.step7
import Book1.Prop09.step8
import Book1.Prop09.step9
import Book1.Prop09.hfa
import Book1.Prop09.hangle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_9 : ∀ (a b c : Point) (AB AC : Line),
  formRectilinearAngle b a c AB AC ∧ AB ≠ AC →
  ∃ f : Point, f ≠ a ∧ (∠ b:a:f = ∠ c:a:f) := by
  euclid_intros
  euclid_intro_sentence "1.9.0"
    "To cut a given rectilinear angle in half.  Let $BAC$ be the given rectilinear angle. So it is required to cut it in half. "

  euclid_apply (point_between_points_shorter_than AB a b (a─c)) as d
  euclid_sentence "1.9.1"
    "Let the point $D$ have been taken at random on $AB$,"
    (step1 : between a d b) := by euclid_apply (helper_1_9_step1 a b d (by euclid_assumption "" (show between a d b; assumption)))

  euclid_apply (proposition_3 a c a d AC AB) as e
  euclid_sentence "1.9.2"
    "and let $AE$, equal to $AD$,  have been cut off from $AC$  [Prop.~1.3],"
    (step2 : between a e c ∧ |(a─e)| = |(a─d)|) := by euclid_apply (helper_1_9_step2 a c d e (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)))

  euclid_apply (line_from_points d e) as DE
  euclid_sentence "1.9.3"
    "and let $DE$ have been joined."
    (step3 : distinctPointsOnLine d e DE) := by euclid_apply (helper_1_9_step3 a b c d e AB AC DE (by euclid_assumption "" (show AB ≠ AC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)))

  euclid_apply (proposition_1' d e a DE) as f
  euclid_apply (line_from_points e f) as EF
  euclid_apply (line_from_points d f) as DF
  euclid_sentence "1.9.4"
    "And let the equilateral triangle $DEF$ have been constructed upon $DE$ [Prop.~1.1],"
    (step4 : formTriangle d e f DE EF DF ∧ |(f─d)| = |(d─e)| ∧ |(f─e)| = |(d─e)|) := by euclid_apply (helper_1_9_step4 d e f DE EF DF (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show ¬f.onLine DE; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)))

  euclid_apply (line_from_points a f) as AF
  euclid_sentence "1.9.5"
    "and let $AF$ have been joined."
    (step5 : distinctPointsOnLine a f AF) := by euclid_apply (helper_1_9_step5 a f DE AF (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬f.onLine DE; assumption)) (by euclid_assumption "" (show ¬a.onLine DE; assumption)) (by euclid_assumption "" (show ¬f.sameSide a DE; assumption)))

  euclid_wts "1.9.6"
    "I say that the angle $BAC$ has been cut in half by the straight-line $AF$. "

  -- pairing DA,AF = EA,AF respectively; the |(a─f)|=|(a─f)| conjunct is the common side AF.
  -- @assumption_valid
  have step7_assumption1 : |(a─d)| = |(a─e)| := by linarith
  -- @assumption_valid
  have step7_assumption2 : |(a─f)| = |(a─f)| := by rfl
  -- @assumption ("$AD$ is equal to  $AE$", |(a─d)| = |(a─e)|)
  -- @assumption ("$AF$ is common", |(a─f)| = |(a─f)|)
  euclid_sentence "1.9.7"
    "For since $AD$ is equal to  $AE$, and $AF$ is common, the two (straight-lines) $DA$, $AF$ are equal to the two (straight-lines) $EA$, $AF$, respectively."
    (step7 : |(d─a)| = |(e─a)| ∧ |(a─f)| = |(a─f)|) := by euclid_apply (helper_1_9_step7 a d e f (by euclid_assumption "$AD$ is equal to  $AE$" (show |(a─d)| = |(a─e)|; assumption)) (by euclid_assumption "$AF$ is common" (show |(a─f)| = |(a─f)|; assumption)))

  euclid_sentence "1.9.8"
    "And the base $DF$ is equal to the base $EF$."
    (step8 : |(d─f)| = |(e─f)|) := by euclid_apply (helper_1_9_step8 d e f (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)))

  euclid_sentence "1.9.9"
    "Thus, angle $DAF$ is equal to angle $EAF$ [Prop.~1.8]. "
    (step9 : ∠ d:a:f = ∠ e:a:f) := by euclid_apply (helper_1_9_step9 a b c d e f AB AC DE EF DF AF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬f.onLine DE; assumption)) (by euclid_assumption "" (show ¬a.onLine DE; assumption)) (by euclid_assumption "" (show ¬f.sameSide a DE; assumption)) (by euclid_assumption "" (show AB ≠ AC; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─e)|; assumption)) (by euclid_assumption "" (show |(f─d)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(e─f)|; assumption)))

  use f
  have hfa : f ≠ a := by euclid_apply (helper_1_9_hfa a f AF (by euclid_assumption "" (show distinctPointsOnLine a f AF; assumption)))
  have hangle : ∠ b:a:f = ∠ c:a:f := by euclid_apply (helper_1_9_hangle a b c d e f AB AC AF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show f ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:f = ∠ e:a:f; assumption)))
  exact ⟨hfa, hangle⟩
  euclid_conclude_sentence "1.9.10"
    "Thus, the given rectilinear angle $BAC$ has been cut in half by the straight-line $AF$. (Which is) the very thing it was required to do."

end Elements.Book1
