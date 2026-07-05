import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_41 : ∀ (a b c d e : Point) (AE BC AB CD BE CE : Line),
  formParallelogram a d b c AE BC AB CD ∧ formTriangle e b c BE BC CE ∧ e.onLine AE ∧ ¬(AE.intersectsLine  BC) →
  (Triangle.area △ a:b:c : ℝ) + (Triangle.area △ a:c:d) = (Triangle.area △ e:b:c) + (Triangle.area △ e :b :c) := by
  euclid_intros
  euclid_intro_sentence "1.41.0"
    "If a parallelogram has the same base as a triangle, and is between the same parallels, then the parallelogram is double (the area) of the triangle.  For let parallelogram $ABCD$ have the same base $BC$ as triangle $EBC$, and let it be between the same parallels, $BC$ and $AE$. I say that  parallelogram $ABCD$ is double (the area) of triangle $BEC$. "

  euclid_apply (line_from_points a c) as AC
  euclid_sentence "1.41.1"
    "For let $AC$ have been joined."
    (step1 : distinctPointsOnLine a c AC) := by sorry

  -- @assumption_valid
  have step2_assumption1 : distinctPointsOnLine b c BC := by euclid_finish
  -- @assumption_valid
  have step2_assumption2 : ¬(AE.intersectsLine BC) := by assumption
  -- @assumption ("it is on the same base, $BC$,  as ($EBC$)", distinctPointsOnLine b c BC)
  -- @assumption ("between the same parallels, $BC$ and $AE$", ¬(AE.intersectsLine BC))
  euclid_sentence "1.41.2"
    "So triangle $ABC$ is equal to triangle $EBC$. For it is on the same base, $BC$,  as ($EBC$), and between the same parallels, $BC$ and $AE$ [Prop.~1.37]."
    (step2 : Triangle.area △ a:b:c = Triangle.area △ e:b:c) := by sorry

  -- @assumption_gap
  have step3_assumption1 : Triangle.area △ a:b:c = Triangle.area △ a:c:d := by sorry
  -- @assumption ("the diagonal $AC$ cuts the former in half", Triangle.area △ a:b:c = Triangle.area △ a:c:d)
  euclid_sentence "1.41.3"
    "But, parallelogram $ABCD$ is double (the area) of triangle $ABC$. For the diagonal $AC$ cuts the former in half [Prop.~1.34]."
    (step3 : Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ a:b:c + Triangle.area △ a:b:c) := by sorry

  euclid_sentence "1.41.4"
    "So parallelogram $ABCD$ is also double (the area) of triangle $EBC$. "
    (step4 : Triangle.area △ a:b:c + Triangle.area △ a:c:d = Triangle.area △ e:b:c + Triangle.area △ e:b:c) := by sorry

  exact step4
  euclid_conclude_sentence "1.41.5"
    "Thus, if a parallelogram has the same base as a triangle, and is between the same parallels, then the parallelogram is double (the area) of the triangle. (Which is) the very thing it was required to show."

end Elements.Book1
