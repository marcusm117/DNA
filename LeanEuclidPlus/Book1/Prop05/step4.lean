import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step4 (a b c f g : Point)
    (h1 : |(a─g)| = |(a─f)|) (h2 : |(a─b)| = |(a─c)|) :
    (|(f─a)| = |(g─a)|) ∧ (|(a─c)| = |(a─b)|) := by
  constructor <;> euclid_finish

end Elements.Book1
