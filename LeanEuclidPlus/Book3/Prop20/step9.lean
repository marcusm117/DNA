import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step9 (d e g : Point) (DEG : Line) (ABC : Circle)
    (h_e_centre : e.isCentre ABC) (h_d_circ : d.onCircle ABC)
    (h_d_DEG : d.onLine DEG) (h_e_DEG : e.onLine DEG)
    (h_g_circ : g.onCircle ABC) (h_g_DEG : g.onLine DEG) (h_bet : between g e d) :
    distinctPointsOnLine d e DEG ∧ g.onCircle ABC ∧ between d e g := by
  euclid_finish

end Elements.Book3
