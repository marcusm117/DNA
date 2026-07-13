import SystemE
import Book3.Prop23.step1
import Book3.Prop23.step2
import Book3.Prop23.step3
import Book3.Prop23.step4
import Book3.Prop23.step5
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_23 : ∀ (a b c d : Point) (AB : Line) (ACB ADB : Circle),
  distinctPointsOnLine a b AB ∧
  a.onCircle ACB ∧ b.onCircle ACB ∧ c.onCircle ACB ∧
  a.onCircle ADB ∧ b.onCircle ADB ∧ d.onCircle ADB ∧
  c.sameSide d AB ∧
  between a c d ∧
  ∠ a:c:b = ∠ a:d:b ∧
  ACB ≠ ADB →
  False :=
by
  euclid_intros
  euclid_intro_sentence "3.23.0"
    "Two similar and unequal segments of circles cannot be constructed on the same side of the same straight-line."

  euclid_sentence "3.23.1"
    "For, if possible, let the two similar and unequal segments of circles, $ACB$ and $ADB$, be constructed on the same side of the same straight-line $AB$."
    (step1 : c.sameSide d AB ∧ ACB ≠ ADB ∧ ∠ a:c:b = ∠ a:d:b) := by euclid_apply (helper_3_23_step1 a b c d AB ACB ADB (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show ACB ≠ ADB; assumption)) (by euclid_assumption "" (show ∠ a:c:b = ∠ a:d:b; assumption)))

  euclid_apply (line_from_points a d) as ACD
  euclid_sentence "3.23.2"
    "And let $ACD$ be drawn through (the segments),"
    (step2 : a.onLine ACD ∧ c.onLine ACD ∧ d.onLine ACD) := by euclid_apply (helper_3_23_step2 a c d ACD (by euclid_assumption "" (show a.onLine ACD; assumption)) (by euclid_assumption "" (show d.onLine ACD; assumption)) (by euclid_assumption "" (show between a c d; assumption)))

  euclid_apply (line_from_points c b) as CB
  euclid_apply (line_from_points d b) as DB
  euclid_sentence "3.23.3"
    "and let $CB$ and $DB$ be joined."
    (step3 : distinctPointsOnLine c b CB ∧ distinctPointsOnLine d b DB) := by euclid_apply (helper_3_23_step3 b c d AB CB DB (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)))

  -- @assumption_valid
  have step4_assumption1 : ∠ a:c:b = ∠ a:d:b := by assumption
  -- @assumption ("segment $ACB$ is similar to segment $ADB$", ∠ a:c:b = ∠ a:d:b)
  euclid_sentence "3.23.4"
    "Therefore, since segment $ACB$ is similar to segment $ADB$, and similar segments of circles are those accepting equal angles [Def.~3.11], angle $ACB$ is thus equal to $ADB$, the external to the internal."
    (step4 : ∠ a:c:b = ∠ a:d:b) := by euclid_apply (helper_3_23_step4 a b c d (by euclid_assumption "segment $ACB$ is similar to segment $ADB$" (show ∠ a:c:b = ∠ a:d:b; assumption)))

  euclid_sentence "3.23.5"
    "The very thing is impossible [Prop.~1.16]."
    (step5 : False) := by euclid_apply (helper_3_23_step5 a b c d AB ACD CB DB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine ACD; assumption)) (by euclid_assumption "" (show c.onLine ACD; assumption)) (by euclid_assumption "" (show d.onLine ACD; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show ∠ a:c:b = ∠ a:d:b; assumption)))

  exact step5

  euclid_conclude_sentence "3.23.6"
    "Thus, two similar and unequal segments of circles cannot be constructed on the same side of the same straight-line."

end Elements.Book3
