import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_hFEB_int (f : Point) (CDE : Circle) (FEB : Line)
    (hfCDE : f.isCentre CDE) (hfFEB : f.onLine FEB)
    : FEB.intersectsCircle CDE := by
  euclid_apply (center_inside_circle f CDE)
  euclid_apply (intersection_circle_line_2 f CDE FEB)
  assumption

end Elements.Book3
