import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step24_pyth (d e f : Point) (DA : Line)
    (hdfe : ∠ d:f:e = ∟)
    (hf_DA : f.onLine DA) (hd_DA : d.onLine DA) (hne_DA : ¬ e.onLine DA) (hdf : d ≠ f) :
    |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points e d) as ED
  euclid_apply (line_from_points f d) as FD
  euclid_apply (proposition_47 f e d FE ED FD)
  euclid_finish

end Elements.Book3
