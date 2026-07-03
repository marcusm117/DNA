import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_1_step5 (a b c : Point) (ACE : Circle)
    (h1 : b.isCentre ACE) (h2 : a.onCircle ACE) (h3 : c.onCircle ACE) :
    |(b─c)| = |(b─a)| := by
  exact point_on_circle_onlyif b a c ACE ⟨h1, h2, h3⟩

end Elements.Book1
