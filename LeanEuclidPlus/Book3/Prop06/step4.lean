import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step4 (ABC : Circle) (f c b : Point)
  (hcABC : c.onCircle ABC) (hbABC : b.onCircle ABC)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : f.isCentre ABC)   -- "point $F$ is the center of the circle $ABC$"
  : |(f─c)| = |(f─b)| := by
  euclid_apply (point_on_circle_onlyif f b c ABC)
  euclid_finish

end Elements.Book3
