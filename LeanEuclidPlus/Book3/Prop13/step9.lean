import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- BH = HD: both b and d lie on EBFD whose centre is h, so both are radii.
theorem helper_3_13_step9 (EBFD : Circle) (b h d : Point)
    (hcenEBFD : h.isCentre EBFD) (hb_EBFD : b.onCircle EBFD) (hd_EBFD : d.onCircle EBFD) :
    |(b─h)| = |(h─d)| := by euclid_finish

end Elements.Book3
