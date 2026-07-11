import SystemE
set_option linter.unusedVariables false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem test_direct (a f g : Point) (ABC ADE : Circle)
    (left : a.onCircle ABC)
    (left_1 : a.onCircle ADE)
    (left_2 : ¬ABC.intersectsCircle ADE)
    (left_3 : g.insideCircle ABC)
    (left_4 : f.isCentre ABC)
    (left_5 : g.isCentre ADE)
    (right_5 : f ≠ g)
    : between f g a := by
  euclid_finish

end Elements.Book3
