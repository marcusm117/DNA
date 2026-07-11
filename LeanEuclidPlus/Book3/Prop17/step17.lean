import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step17 (b : Point) (BCD : Circle)
    (hb_onBCD : b.onCircle BCD) :
    b.onCircle BCD :=
  hb_onBCD

end Elements.Book3
