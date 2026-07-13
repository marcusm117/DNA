import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_37_step12_pyth (d e f : Point) (ABC : Circle) (DE FE FD : Line)
    (h_e_DE : e.onLine DE) (h_d_DE : d.onLine DE)
    (h_f_FE : f.onLine FE) (h_e_FE : e.onLine FE)
    (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD)
    (h_fe : f ≠ e) (h_fd : f ≠ d)
    (h_e_circ : e.onCircle ABC) (h_d_noc : ¬ d.onCircle ABC)
    (h_foffDE : ¬ f.onLine DE) (h_angle : ∠ f:e:d = ∟) :
    |(f─d)| * |(f─d)| = |(f─e)| * |(f─e)| + |(e─d)| * |(e─d)| := by
  euclid_apply (proposition_47 e f d FE FD DE)
  euclid_finish

end Elements.Book3
