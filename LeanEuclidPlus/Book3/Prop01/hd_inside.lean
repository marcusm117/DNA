import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_hd_inside (ABC : Circle) (a b d : Point)
    (h_a_on : a.onCircle ABC) (h_b_on : b.onCircle ABC)
    (h_bet : between a d b) :
    d.insideCircle ABC :=
  circle_points_between a b d ABC
    ⟨fun h => h.2 h_a_on, fun h => h.2 h_b_on, h_bet⟩

end Elements.Book3
