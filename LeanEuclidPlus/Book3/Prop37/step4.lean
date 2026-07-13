import SystemE
import Book3.Prop18.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step4 (d e f : Point) (ABC : Circle) (DE : Line)
    (h_e_circ : e.onCircle ABC) (h_e_DE : e.onLine DE) (h_nint : ¬ DE.intersectsCircle ABC)
    (h_f_cen : f.isCentre ABC) (h_fe : f ≠ e) (h_d_DE : d.onLine DE)
    (h_d_noc : ¬ d.onCircle ABC) :
    ∠ f:e:d = ∟ := by
  euclid_apply (proposition_18 e f ABC DE)
  euclid_finish

end Elements.Book3
