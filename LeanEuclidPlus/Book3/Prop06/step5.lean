import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step5 (CDE : Circle) (f c e : Point)
  (hcCDE : c.onCircle CDE) (heCDE : e.onCircle CDE)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : f.isCentre CDE)   -- "point $F$ is the center of the circle $CDE$"
  : |(f─c)| = |(f─e)| := by
  euclid_apply (point_on_circle_onlyif f e c CDE)
  euclid_finish

end Elements.Book3
