import SystemE
import Book1.Prop01.variants
import Book1.Prop09.variants
import Book1.Prop10.step1
import Book1.Prop10.step2
import Book1.Prop10.step4
import Book1.Prop10.step5
import Book1.Prop10.step6
import Book1.Prop10.hbet
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_10 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ d : Point, (between a d b) ∧ (|(a─d)| = |(d─b)|) := by
  euclid_intros
  euclid_intro_sentence "1.10.0"
    "To cut a given finite straight-line in half. Let $AB$ be the given finite straight-line. So it is required to cut the finite straight-line $AB$ in half. "

  euclid_apply (proposition_1 a b AB) as c
  euclid_apply (line_from_points c a) as AC
  euclid_apply (line_from_points c b) as BC
  euclid_sentence "1.10.1"
    "Let the equilateral triangle $ABC$ have been constructed upon  ($AB$) [Prop.~1.1],"
    (step1 : formTriangle a b c AB BC AC ∧ |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|) := by euclid_apply (helper_1_10_step1 a b c AB AC BC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(c─a)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(c─b)| = |(a─b)|; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)))

  euclid_apply (proposition_9' c a b AC BC) as d'
  euclid_apply (line_from_points c d') as CD
  euclid_apply (intersection_lines CD AB) as d
  euclid_sentence "1.10.2"
    "and let the angle $ACB$ have been cut in half by the straight-line $CD$ [Prop.~1.9]."
    (step2 : ∠ a:c:d = ∠ b:c:d) := by euclid_apply (helper_1_10_step2 a b c d d' AB AC BC CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d'.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d'.sameSide b AC; assumption)) (by euclid_assumption "" (show d'.sameSide a BC; assumption)) (by euclid_assumption "" (show ∠ a:c:d' = ∠ b:c:d'; assumption)))

  euclid_wts "1.10.3"
    "I say that the straight-line $AB$ has been cut in half at  point $D$. "

  -- @assumption_valid
  have step4_assumption1 : |(a─c)| = |(c─b)| := by euclid_finish
  -- @assumption_valid
  have step4_assumption2 : |(c─d)| = |(c─d)| := by rfl
  -- @assumption ("$AC$ is equal to $CB$", |(a─c)| = |(c─b)|)
  -- @assumption ("$CD$ (is) common", |(c─d)| = |(c─d)|)
  euclid_sentence "1.10.4"
    "For since $AC$ is equal to $CB$, and $CD$ (is) common, the two (straight-lines) $AC$, $CD$ are equal to the two (straight-lines) $BC$, $CD$, respectively."
    (step4 : |(a─c)| = |(b─c)| ∧ |(c─d)| = |(c─d)|) := by euclid_apply (helper_1_10_step4 a b c d (by euclid_assumption "$AC$ is equal to $CB$" (show |(a─c)| = |(c─b)|; assumption)) (by euclid_assumption "$CD$ (is) common" (show |(c─d)| = |(c─d)|; assumption)))

  -- recalls the construction bisection (step2) for use in [Prop.~1.4]
  euclid_sentence "1.10.5"
    "And the angle $ACD$ is equal to the angle $BCD$."
    (step5 : ∠ a:c:d = ∠ b:c:d) := by euclid_apply (helper_1_10_step5 a b c d d' AB AC BC CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d'.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d'.sameSide b AC; assumption)) (by euclid_assumption "" (show d'.sameSide a BC; assumption)) (by euclid_assumption "" (show ∠ a:c:d' = ∠ b:c:d'; assumption)))

  euclid_sentence "1.10.6"
    "Thus, the base $AD$ is equal to the base $BD$ [Prop.~1.4]."
    (step6 : |(a─d)| = |(d─b)|) := by euclid_apply (helper_1_10_step6 a b c d d' AB AC BC CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d'.onLine CD; assumption)) (by euclid_assumption "" (show d'.sameSide b AC; assumption)) (by euclid_assumption "" (show d'.sameSide a BC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show |(c─a)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(c─b)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∠ b:c:d; assumption)))

  have hbet : between a d b := by euclid_apply (helper_1_10_hbet a b c d d' AB AC BC CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d'.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d'.sameSide b AC; assumption)) (by euclid_assumption "" (show d'.sameSide a BC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show |(c─a)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(c─b)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(a─d)| = |(d─b)|; assumption)))
  exact ⟨d, hbet, step6⟩
  euclid_conclude_sentence "1.10.7"
    "Thus, the given finite straight-line $AB$ has been cut in half at  (point) $D$.  (Which is) the very thing it was required to do."

end Elements.Book1
