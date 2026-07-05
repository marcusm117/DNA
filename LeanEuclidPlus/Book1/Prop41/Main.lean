import SystemE
import Book1.Prop41.step1
import Book1.Prop41.step2
import Book1.Prop41.step3
import Book1.Prop41.step4
import Book1.Prop41.step3_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_41 : ∀ (a b c d e : Point) (AE BC AB CD BE CE : Line),
  formParallelogram a d b c AE BC AB CD ∧ formTriangle e b c BE BC CE ∧ e.onLine AE ∧ ¬(AE.intersectsLine  BC) →
  (Triangle.area △ a:b:c : ℝ) + (Triangle.area △ a:c:d) = (Triangle.area △ e:b:c) + (Triangle.area △ e :b :c) := by
  euclid_intros
  euclid_intro_sentence "1.41.0"
    "If a parallelogram has the same base as a triangle, and is between the same parallels, then the parallelogram is double (the area) of the triangle.  For let parallelogram $ABCD$ have the same base $BC$ as triangle $EBC$, and let it be between the same parallels, $BC$ and $AE$. I say that  parallelogram $ABCD$ is double (the area) of triangle $BEC$. "

  euclid_apply (line_from_points a c) as AC
  euclid_sentence "1.41.1"
    "For let $AC$ have been joined."
    (step1 : distinctPointsOnLine a c AC) := by euclid_apply (helper_1_41_step1 a b c CD AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)))

  -- @assumption_valid
  have step2_assumption1 : distinctPointsOnLine b c BC := by euclid_finish
  -- @assumption_valid
  have step2_assumption2 : ¬(AE.intersectsLine BC) := by assumption
  -- @assumption ("it is on the same base, $BC$,  as ($EBC$)", distinctPointsOnLine b c BC)
  -- @assumption ("between the same parallels, $BC$ and $AE$", ¬(AE.intersectsLine BC))
  euclid_sentence "1.41.2"
    "So triangle $ABC$ is equal to triangle $EBC$. For it is on the same base, $BC$,  as ($EBC$), and between the same parallels, $BC$ and $AE$ [Prop.~1.37]."
    (step2 : Triangle.area △ a:b:c = Triangle.area △ e:b:c) := by euclid_apply (helper_1_41_step2 a b c e AE BC AB CD AC BE CE (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show BE ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ CE; assumption)) (by euclid_assumption "" (show CE ≠ BE; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show distinctPointsOnLine a c AC; assumption)) (by euclid_assumption "it is on the same base, $BC$,  as ($EBC$)" (show distinctPointsOnLine b c BC; assumption)) (by euclid_assumption "between the same parallels, $BC$ and $AE$" (show ¬(AE.intersectsLine BC); assumption)))

  -- @assumption_gap
  have step3_assumption1 : Triangle.area △ a:b:c = Triangle.area △ a:c:d := by euclid_apply (helper_1_41_step3_assumption1 a b c d AE BC AB CD AC (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine AE; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬AE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show distinctPointsOnLine a c AC; assumption)))
  -- @assumption ("the diagonal $AC$ cuts the former in half", Triangle.area △ a:b:c = Triangle.area △ a:c:d)
  euclid_sentence "1.41.3"
    "But, parallelogram $ABCD$ is double (the area) of triangle $ABC$. For the diagonal $AC$ cuts the former in half [Prop.~1.34]."
    (step3 : Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ a:b:c + Triangle.area △ a:b:c) := by euclid_apply (helper_1_41_step3 a b c d AE BC AB CD AC (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine AE; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬AE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show distinctPointsOnLine a c AC; assumption)) (by euclid_assumption "the diagonal $AC$ cuts the former in half" (show Triangle.area △ a:b:c = Triangle.area △ a:c:d; assumption)))

  euclid_sentence "1.41.4"
    "So parallelogram $ABCD$ is also double (the area) of triangle $EBC$. "
    (step4 : Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ e:b:c + Triangle.area △ e:b:c) := by euclid_apply (helper_1_41_step4 (by euclid_assumption "" (show Triangle.area △ a:b:c = Triangle.area △ e:b:c; assumption)) (by euclid_assumption "" (show Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ a:b:c + Triangle.area △ a:b:c; assumption)))

  exact step4
  euclid_conclude_sentence "1.41.5"
    "Thus, if a parallelogram has the same base as a triangle, and is between the same parallels, then the parallelogram is double (the area) of the triangle. (Which is) the very thing it was required to show."

end Elements.Book1
