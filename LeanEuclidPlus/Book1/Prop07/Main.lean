import SystemE
import Book1.Prop07.step1
import Book1.Prop07.step2
import Book1.Prop07.step3
import Book1.Prop07.step4
import Book1.Prop07.step5
import Book1.Prop07.step6
import Book1.Prop07.step7
import Book1.Prop07.step8
import Book1.Prop07.step9
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_7 : ∀ (a b c d : Point) (AB AC CB AD DB : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c AC ∧ distinctPointsOnLine c b CB ∧
  distinctPointsOnLine a d AD ∧ distinctPointsOnLine d b DB ∧ (c.sameSide d AB) ∧ c ≠ d ∧
  (|(a─c)| = |(a─d)|) ∧ (|(c─b)| = |(d─b)|) → False := by
  euclid_intros
  euclid_intro_sentence "1.7.0"
    "On the same straight-line, two other straight-lines  equal, respectively, to  two (given) straight-lines (which meet) cannot be constructed (meeting) at  a different point on the same side (of the straight-line), but having the same ends as the given straight-lines.      For, if possible, let the two straight-lines $AC$, $CB$, equal to two other straight-lines $AD$, $DB$, respectively, have been constructed on the same straight-line $AB$, meeting at different points, $C$ and $D$, on the same side (of $AB$), and having the same ends (on $AB$)."

  euclid_sentence "1.7.1"
    "So $CA$ is equal to $DA$, having the same end $A$ as it,"
    (step1 : |(c─a)| = |(d─a)|) := by euclid_apply (helper_1_7_step1 a c d (by euclid_assumption "" (show |(a─c)| = |(a─d)|; assumption)))

  euclid_sentence "1.7.2"
    "and $CB$ is equal to $DB$, having the same end $B$ as it."
    (step2 : |(c─b)| = |(d─b)|) := by euclid_apply (helper_1_7_step2 c d b (by euclid_assumption "" (show |(c─b)| = |(d─b)|; assumption)))

  euclid_apply (line_from_points c d) as CD
  euclid_sentence "1.7.3"
    "And let $CD$ have been joined [Post.~1]. "
    (step3 : c.onLine CD ∧ d.onLine CD) := by euclid_apply (helper_1_7_step3 c d CD (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)))

  -- @assumption_valid
  have step4_assumption1 : |(a─c)| = |(a─d)| := by assumption
  -- @assumption ("$AC$ is equal to $AD$", |(a─c)| = |(a─d)|)
  euclid_sentence "1.7.4"
    "Therefore, since $AC$ is equal to $AD$,  the angle $ACD$ is also equal to angle $ADC$ [Prop.~1.5]."
    (step4 : ∠ a:c:d = ∠ a:d:c) := by euclid_apply (helper_1_7_step4 a c d AB AC CD AD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "$AC$ is equal to $AD$" (show |(a─c)| = |(a─d)|; assumption)))

  euclid_sentence "1.7.5"
    "Thus, $ADC$ (is) greater than $DCB$ [C.N.~5]."
    (step5 : ∠ a:d:c > ∠ d:c:b) := by euclid_apply (helper_1_7_step5 a b c d AB AC CB AD DB CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(c─b)| = |(d─b)|; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∠ a:d:c; assumption)))

  euclid_sentence "1.7.6"
    "Thus, $CDB$ is much greater than $DCB$ [C.N.~5]."
    (step6 : ∠ c:d:b > ∠ d:c:b) := by euclid_apply (helper_1_7_step6 a b c d AB AC CB AD DB CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(c─b)| = |(d─b)|; assumption)) (by euclid_assumption "" (show ∠ a:d:c > ∠ d:c:b; assumption)))

  -- @assumption_valid
  have step7_assumption1 : |(c─b)| = |(d─b)| := by assumption
  -- @assumption ("$CB$ is equal to $DB$", |(c─b)| = |(d─b)|)
  euclid_sentence "1.7.7"
    "Again, since  $CB$ is equal to $DB$, the angle $CDB$ is also equal to angle $DCB$ [Prop.~1.5]."
    (step7 : ∠ c:d:b = ∠ d:c:b) := by euclid_apply (helper_1_7_step7 a b c d AB AC CB AD DB CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─d)|; assumption)) (by euclid_assumption "$CB$ is equal to $DB$" (show |(c─b)| = |(d─b)|; assumption)))

  -- recalls step6: ∠CDB was shown much greater than ∠DCB
  euclid_sentence "1.7.8"
    "But it was shown that the former (angle) is also much greater (than the latter)."
    (step8 : ∠ c:d:b > ∠ d:c:b) := by euclid_apply (helper_1_7_step8 c d b (by euclid_assumption "" (show ∠ c:d:b > ∠ d:c:b; assumption)))

  euclid_sentence "1.7.9"
    "The very thing is impossible. "
    (step9 : False) := by euclid_apply (helper_1_7_step9 c d b (by euclid_assumption "" (show ∠ c:d:b = ∠ d:c:b; assumption)) (by euclid_assumption "" (show ∠ c:d:b > ∠ d:c:b; assumption)))

  exact step9
  euclid_conclude_sentence "1.7.10"
    "Thus, on the same straight-line, two other straight-lines equal, respectively, to   two (given) straight-lines  (which meet) cannot be constructed (meeting) at a different point on the same side (of the straight-line), but having the same ends as the given straight-lines. (Which is) the very thing it was required to show."

end Elements.Book1
