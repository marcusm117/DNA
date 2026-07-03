import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_1_step7 (a b c : Point)
    (h1 : |(c─a)| = |(a─b)|) (h2 : |(b─c)| = |(b─a)|) :
    |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| := by
  refine ⟨h1, ?_⟩
  exact (segment_symmetric c b).trans (h2.trans (segment_symmetric b a))

end Elements.Book1
