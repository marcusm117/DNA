import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_2_step7 (d l g : Point) (GKL : Circle)
    (hdl : d.isCentre GKL) (hll : l.onCircle GKL) (hgl : g.onCircle GKL) :
    |(d─l)| = |(d─g)| := by
  euclid_apply (point_on_circle_onlyif d l g GKL)
  euclid_finish

end Elements.Book1
