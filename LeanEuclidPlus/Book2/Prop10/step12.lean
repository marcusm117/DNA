import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step12 (2.10.12): "the angle at C is a right-angle" — restates the perpendicular (step1).
set_option systemE.solverTime 30 in
theorem helper_2_10_step12
  (a c e : Point)
  (hright : ∠ a:c:e = ∟) :
  ∠ a:c:e = ∟ := hright

end Elements.Book2
