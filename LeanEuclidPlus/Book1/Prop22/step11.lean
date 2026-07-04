import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_22_step11 (k f d a a' : Point)
    (h9 : |(f─d)| = |(f─k)|) (h10 : |(f─d)| = |(a─a')|) :
    |(k─f)| = |(a─a')| :=
  (segment_symmetric k f).trans h9.symm |>.trans h10

end Elements.Book1
