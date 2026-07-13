import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hcα₂ (a b c d : Point) (α₂ : Circle)
    (hcentre : d.isCentre α₂) (ha_circ : a.onCircle α₂)
    (hrad1 : |(d─a)| = |(d─b)|) (hrad2 : |(d─b)| = |(d─c)|) :
    c.onCircle α₂ := by
  euclid_finish

end Elements.Book3
