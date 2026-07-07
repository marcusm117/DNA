import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_hDC_int (ABC : Circle) (d : Point) (DC : Line)
    (h_d_inside : d.insideCircle ABC) (h_d_on_DC : d.onLine DC) :
    DC.intersectsCircle ABC :=
  intersection_circle_line_2 d ABC DC ⟨h_d_inside, h_d_on_DC⟩

end Elements.Book3
