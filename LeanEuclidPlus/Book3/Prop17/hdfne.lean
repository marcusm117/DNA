import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_hdfne (a d f e : Point) (BCD AFG : Circle)
    (hcen_BCD : e.isCentre BCD) (hcen_AFG : e.isCentre AFG)
    (hd_onBCD : d.onCircle BCD) (hf_onAFG : f.onCircle AFG)
    (ha_onAFG : a.onCircle AFG)
    (ha_left : ¬a.insideCircle BCD) (ha_right : ¬a.onCircle BCD) : d ≠ f := by
  have hd_inside_AFG : d.insideCircle AFG := by euclid_finish
  euclid_finish

end Elements.Book3
