import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_22_step9
    (f d k : Point) (DKL : Circle)
    (hassump1 : f.isCentre DKL)
    (hdOnDKL : d.onCircle DKL)
    (hkOnDKL : k.onCircle DKL) :
    |(f─d)| = |(f─k)| := by
  euclid_apply (point_on_circle_onlyif f d k DKL)
  euclid_finish

end Elements.Book1
