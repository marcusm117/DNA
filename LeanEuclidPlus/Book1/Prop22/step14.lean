import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_22_step14 (k g h c c' : Point)
    (h12 : |(g─h)| = |(g─k)|) (h13 : |(g─h)| = |(c─c')|) :
    |(k─g)| = |(c─c')| :=
  (segment_symmetric k g).trans (h12.symm.trans h13)

end Elements.Book1
