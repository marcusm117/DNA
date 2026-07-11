import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- BG = GD: both b and d lie on ABDC whose centre is g, so both are radii.
theorem helper_3_13_step6 (ABDC : Circle) (b g d : Point)
    (hcenABDC : g.isCentre ABDC) (hb_ABDC : b.onCircle ABDC) (hd_ABDC : d.onCircle ABDC) :
    |(b─g)| = |(g─d)| := by euclid_finish

end Elements.Book3
