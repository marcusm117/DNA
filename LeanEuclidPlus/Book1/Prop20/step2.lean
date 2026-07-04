import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step2 (a c d : Point) (h : |(a─d)| = |(a─c)|) :
    |(a─d)| = |(c─a)| := by
  euclid_finish

end Elements.Book1
