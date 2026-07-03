import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_1_step10 (a b c : Point)
    (h6 : |(c─a)| = |(a─b)|) (h5 : |(b─c)| = |(b─a)|) :
    |(c─a)| = |(a─b)| ∧ |(a─b)| = |(b─c)| := by
  refine ⟨h6, ?_⟩
  exact (segment_symmetric a b).trans h5.symm

end Elements.Book1
