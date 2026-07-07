import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step4 (ABC : Circle) (c d e : Point) (DC : Line)
    (h_e_on : e.onCircle ABC)
    (h_c_on : c.onCircle ABC)
    (h_d_on_DC : d.onLine DC) (h_c_on_DC : c.onLine DC) (h_e_on_DC : e.onLine DC)
    (h_d_inside : d.insideCircle ABC)
    (h_cNe : c ≠ e) :
    e.onCircle ABC ∧ between c d e :=
  ⟨h_e_on, circle_line_intersections d c e DC ABC
    ⟨h_d_on_DC, h_c_on_DC, h_e_on_DC, h_d_inside, h_c_on, h_e_on, h_cNe⟩⟩

end Elements.Book3
