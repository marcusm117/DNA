import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step7 (ABC : Circle) (g : Point)
    (h_g_center : g.isCentre ABC) :
    g.isCentre ABC := h_g_center

end Elements.Book3
