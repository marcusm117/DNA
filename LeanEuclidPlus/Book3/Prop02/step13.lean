import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step13 (p : Point) (ABC : Circle)
    (habsurd1 : ¬p.outsideCircle ABC) :
    ¬p.outsideCircle ABC := by
  assumption

end Elements.Book3
