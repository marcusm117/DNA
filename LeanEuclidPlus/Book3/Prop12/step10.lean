import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step10 (f a g : Point)
    (step9 : ¬¬between f a g)
    : between f a g :=
  Classical.byContradiction step9

end Elements.Book3
