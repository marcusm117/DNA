import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_99_step3 (a c e : Point)
    (h : |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|) :
    |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)| :=
  h

end Elements.Book2
