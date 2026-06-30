import SystemE
import Mathlib.Tactic.LinearCombination
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

private theorem golden_arith (A M Q F AH BH : ℝ)
    (hA : A = M + M) (hpy : Q * Q = M * M + A * A)
    (hQ : Q = M + F) (hAH : AH = F) (hBH : A = AH + BH) :
    A * BH = AH * AH := by
  subst hQ hA hAH
  linear_combination (-2 * M) * hBH - hpy

theorem helper_2_11_step8_golden
    (a b e f h : Point)
    (step8_bisect : |(a─b)| = |(a─e)| + |(a─e)|)
    (step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|)
    (step8_eb : |(e─b)| = |(a─e)| + |(a─f)|)
    (hah_af : |(a─h)| = |(a─f)|)
    (step8_ahb : |(a─b)| = |(a─h)| + |(b─h)|) :
    |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| := by
  exact golden_arith |(a─b)| |(a─e)| |(e─b)| |(a─f)| |(a─h)| |(b─h)|
    step8_bisect step8_pyth step8_eb hah_af step8_ahb

end Elements.Book2
