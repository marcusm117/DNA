import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_18_step4 (f c b : Point) (ABC : Circle)
    (h_centre : f.isCentre ABC) (h_bon : b.onCircle ABC) (h_con : c.onCircle ABC) :
    |(f─c)| = |(f─b)| := by
  euclid_apply (point_on_circle_onlyif f b c ABC)
  euclid_finish

end Elements.Book3
