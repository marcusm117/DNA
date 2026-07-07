import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_step4 (ABC : Circle) (e c f : Point)
    (hassump1 : e.isCentre ABC)
    (hcABC : c.onCircle ABC) (hfABC : f.onCircle ABC)
    : |(e─c)| = |(e─f)| := by
  euclid_finish

end Elements.Book3
