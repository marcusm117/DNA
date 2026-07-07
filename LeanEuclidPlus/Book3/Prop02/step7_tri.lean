import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step7_tri (a b d : Point) (DA DB AB : Line)
    (hdDA : d.onLine DA) (haDA : a.onLine DA)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hda_ne : d ≠ a) (hdb_ne : d ≠ b) (hab : a ≠ b)
    (hd_AB : ¬d.onLine AB) :
    formTriangle d a b DA AB DB := by
  euclid_finish

end Elements.Book3
