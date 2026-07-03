import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step4 (a b c : Point) (BCD : Circle)
    (h1 : a.isCentre BCD) (h2 : b.onCircle BCD) (h3 : c.onCircle BCD) :
    |(a─c)| = |(a─b)| := by
  exact point_on_circle_onlyif a b c BCD ⟨h1, h2, h3⟩

end Elements.Book1
