import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_35 : ∀ (a b c d e f g : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC ∧
  between a d e ∧ between d e f ∧ g.onLine CD ∧ g.onLine EB →
  Triangle.area △a:b:d + Triangle.area △d:b:c = Triangle.area △e:b:c + Triangle.area △ e:c:f := by
  euclid_intros
  euclid_intro_sentence "1.35.0"
    "Parallelograms which are on the same base and between the same parallels are equal to one another. Let $ABCD$ and $EBCF$ be parallelograms on the same base $BC$, and between the same parallels $AF$ and $BC$. I say that $ABCD$ is equal to parallelogram $EBCF$. "

  -- @assumption_valid
  have step1_assumption1 : formParallelogram a d b c AF BC AB CD := by euclid_finish
  -- @assumption ("$ABCD$ is a parallelogram", formParallelogram a d b c AF BC AB CD)
  euclid_sentence "1.35.1"
    "For since $ABCD$ is a parallelogram, $AD$ is equal to $BC$ [Prop.~1.34]."
    (step1 : |(a─d)| = |(b─c)|) := by sorry

  euclid_sentence "1.35.2"
    "So, for the same (reasons), $EF$ is also equal to $BC$."
    (step2 : |(e─f)| = |(b─c)|) := by sorry

  euclid_sentence "1.35.3"
    "So $AD$ is also equal to $EF$."
    (step3 : |(a─d)| = |(e─f)|) := by sorry

  euclid_sentence "1.35.4"
    "And $DE$ is common."
    (step4 : distinctPointsOnLine d e AF) := by sorry

  euclid_sentence "1.35.5"
    "Thus, the whole (straight-line) $AE$ is equal to the whole (straight-line) $DF$. "
    (step5 : |(a─e)| = |(d─f)|) := by sorry

  euclid_sentence "1.35.6"
    "And $AB$ is also equal to $DC$."
    (step6 : |(a─b)| = |(d─c)|) := by sorry

  euclid_sentence "1.35.7"
    "So the two (straight-lines) $EA$, $AB$ are equal to the two (straight-lines) $FD$, $DC$, respectively."
    (step7 : |(e─a)| = |(f─d)| ∧ |(a─b)| = |(d─c)|) := by sorry

  euclid_sentence "1.35.8"
    "And angle $FDC$ is equal to angle $EAB$, the external to the internal [Prop.~1.29]."
    (step8 : ∠ f:d:c = ∠ e:a:b) := by sorry

  euclid_sentence "1.35.9"
    "Thus, the base $EB$ is equal to the base $FC$,"
    (step9 : |(e─b)| = |(f─c)|) := by sorry

  euclid_sentence "1.35.10"
    "and triangle $EAB$ will be equal to triangle $DFC$ [Prop.~1.4]."
    (step10 : Triangle.area △ e:a:b = Triangle.area △ d:f:c) := by sorry

  euclid_sentence "1.35.11"
    "Let $DGE$ have been taken away from both. "
    (step11 : Triangle.area △ e:a:b - Triangle.area △ d:g:e = Triangle.area △ d:f:c - Triangle.area △ d:g:e) := by sorry

  euclid_sentence "1.35.12"
    "Thus, the remaining trapezium $ABGD$ is equal to the remaining trapezium $EGCF$."
    (step12 : Triangle.area △ a:b:d + Triangle.area △ b:g:d = Triangle.area △ e:g:c + Triangle.area △ e:c:f) := by sorry

  euclid_sentence "1.35.13"
    "Let triangle $GBC$ have been added to both."
    (step13 : Triangle.area △ a:b:d + Triangle.area △ b:g:d + Triangle.area △ g:b:c =
              Triangle.area △ e:g:c + Triangle.area △ e:c:f + Triangle.area △ g:b:c) := by sorry

  euclid_sentence "1.35.14"
    "Thus, the whole parallelogram $ABCD$ is equal to the whole parallelogram $EBCF$. "
    (step14 : Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:b:c + Triangle.area △ e:c:f) := by sorry

  exact step14
  euclid_conclude_sentence "1.35.15"
    "Thus, parallelograms which are on the same base and between the same parallels are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
