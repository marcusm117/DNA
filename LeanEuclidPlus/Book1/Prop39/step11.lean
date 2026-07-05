import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_39_step11
    (d e b c : Point) (AD BC : Line)
    (step7 : Triangle.area △ d:b:c = Triangle.area △ e:b:c)
    (step8 : Triangle.area △ d:b:c ≠ Triangle.area △ e:b:c)
    : ¬(AD.intersectsLine BC) :=
  fun _ => absurd step7 step8

end Elements.Book1
