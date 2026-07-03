import SystemE
import Book.Prop01
import Book.Prop03
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_9 : ∀ (a b c : Point) (AB AC : Line),
  formRectilinearAngle b a c AB AC ∧ AB ≠ AC →
  ∃ f : Point, f ≠ a ∧ (∠ b:a:f = ∠ c:a:f) := by
  euclid_intros
  euclid_intro_sentence "1.9.0"
    "To cut a given rectilinear angle in half.  Let $BAC$ be the given rectilinear angle. So it is required to cut it in half. "

  euclid_apply (point_between_points_shorter_than AB a b (a─c)) as d
  euclid_sentence "1.9.1"
    "Let the point $D$ have been taken at random on $AB$,"
    (step1 : between a d b) := by sorry

  euclid_apply (proposition_3 a c a d AC AB) as e
  euclid_sentence "1.9.2"
    "and let $AE$, equal to $AD$,  have been cut off from $AC$  [Prop.~1.3],"
    (step2 : between a e c ∧ |(a─e)| = |(a─d)|) := by sorry

  euclid_apply (line_from_points d e) as DE
  euclid_sentence "1.9.3"
    "and let $DE$ have been joined."
    (step3 : distinctPointsOnLine d e DE) := by sorry

  euclid_apply (proposition_1' d e a DE) as f
  euclid_apply (line_from_points e f) as EF
  euclid_apply (line_from_points d f) as DF
  euclid_sentence "1.9.4"
    "And let the equilateral triangle $DEF$ have been constructed upon $DE$ [Prop.~1.1],"
    (step4 : formTriangle d e f DE EF DF ∧ |(f─d)| = |(d─e)| ∧ |(f─e)| = |(d─e)|) := by sorry

  euclid_apply (line_from_points a f) as AF
  euclid_sentence "1.9.5"
    "and let $AF$ have been joined."
    (step5 : distinctPointsOnLine a f AF) := by sorry

  euclid_sentence "1.9.6"
    "I say that the angle $BAC$ has been cut in half by the straight-line $AF$. "
    (step6 : ∠ b:a:f = ∠ c:a:f) := by sorry

  -- @assumption ("$AD$ is equal to  $AE$", |(a─d)| = |(a─e)|)
  -- @assumption ("$AF$ is common", distinctPointsOnLine a f AF)
  -- pairing DA,AF = EA,AF respectively; the |(a─f)|=|(a─f)| conjunct is the common side AF.
  euclid_sentence "1.9.7"
    "For since $AD$ is equal to  $AE$, and $AF$ is common, the two (straight-lines) $DA$, $AF$ are equal to the two (straight-lines) $EA$, $AF$, respectively."
    (step7 : |(d─a)| = |(e─a)| ∧ |(a─f)| = |(a─f)|) := by sorry

  euclid_sentence "1.9.8"
    "And the base $DF$ is equal to the base $EF$."
    (step8 : |(d─f)| = |(e─f)|) := by sorry

  euclid_sentence "1.9.9"
    "Thus, angle $DAF$ is equal to angle $EAF$ [Prop.~1.8]. "
    (step9 : ∠ d:a:f = ∠ e:a:f) := by sorry

  use f
  have hfa : f ≠ a := by sorry
  exact ⟨hfa, step6⟩
  euclid_conclude_sentence "1.9.10"
    "Thus, the given rectilinear angle $BAC$ has been cut in half by the straight-line $AF$. (Which is) the very thing it was required to do."

end Elements.Book1
