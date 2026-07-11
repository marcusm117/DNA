import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_habne (a b : Point) (BCD : Circle)
    (ha_not_on : ¬a.onCircle BCD)
    (hb_onBCD : b.onCircle BCD) :
    a ≠ b := by
  euclid_finish

end Elements.Book3
