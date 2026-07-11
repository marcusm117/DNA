import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step9 (f a g : Point)
    (habsurd1 : ¬¬between f a g)
    : ¬¬between f a g :=
  habsurd1

end Elements.Book3
