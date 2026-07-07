import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step20 (DC : Line) (c e f : Point)
    (h_c_on_DC : c.onLine DC)
    (h_e_on_DC : e.onLine DC)
    (h_bet_cfe : between c f e) :
    f.onLine DC :=
  between_same_line_in c f e DC ⟨h_bet_cfe, h_c_on_DC, h_e_on_DC⟩

end Elements.Book3
