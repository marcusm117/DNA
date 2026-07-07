import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step8 (ABC CDE : Circle)
    (habsurd1 : ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE))
    : ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE) := habsurd1

end Elements.Book3
