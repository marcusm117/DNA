import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.19: "And it was also shown (to be) equilateral." Restates the equilateral chain established in
   step12. -/
theorem helper_2_4_step19 (b c g k : Point)
    (hstep12 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) :
    |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)| := by
  exact hstep12

end Elements.Book2
