import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hbα₃ (a b e : Point) (α₃ : Circle)
    (hcentre : e.isCentre α₃) (ha_circ : a.onCircle α₃)
    (hrad : |(e─a)| = |(e─b)|) :
    b.onCircle α₃ := by
  euclid_finish

end Elements.Book3
