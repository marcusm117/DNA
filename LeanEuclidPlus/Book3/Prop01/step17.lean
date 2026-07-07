import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step17 (ABC : Circle) (g : Point)
    (habsurd1 : ¬g.isCentre ABC) :
    ¬g.isCentre ABC :=
  habsurd1

end Elements.Book3
