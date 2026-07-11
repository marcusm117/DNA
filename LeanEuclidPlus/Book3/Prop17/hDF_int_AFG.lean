import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_hDF_int_AFG (a d e : Point) (BCD AFG : Circle) (DF_line : Line)
    (hcen_BCD : e.isCentre BCD) (hcen_AFG : e.isCentre AFG) (ha_onAFG : a.onCircle AFG)
    (hd_onBCD : d.onCircle BCD) (hd_onDF : d.onLine DF_line)
    (ha_left : ¬a.insideCircle BCD) (ha_right : ¬a.onCircle BCD) :
    DF_line.intersectsCircle AFG := by
  have hd_inside_AFG : d.insideCircle AFG := by euclid_finish
  exact intersection_circle_line_2 d AFG DF_line ⟨hd_inside_AFG, hd_onDF⟩

end Elements.Book3
