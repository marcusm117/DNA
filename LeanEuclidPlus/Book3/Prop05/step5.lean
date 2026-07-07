import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_step5 (CDG : Circle) (e c g : Point)
    (hassump1 : e.isCentre CDG)
    (hcCDG : c.onCircle CDG) (hgCDG : g.onCircle CDG)
    : |(e─c)| = |(e─g)| := by
  euclid_finish

end Elements.Book3
