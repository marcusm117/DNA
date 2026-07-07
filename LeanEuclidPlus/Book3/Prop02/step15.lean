import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step15 (p : Point) (ABC : Circle)
    (hstep13 : ¬p.outsideCircle ABC)
    (hstep14 : ¬p.onCircle ABC) :
    p.insideCircle ABC := by
  by_contra h
  exact hstep13 ⟨h, hstep14⟩

end Elements.Book3
