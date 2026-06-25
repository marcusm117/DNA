import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/- 1.6.2: Let AB be greater. The case hypothesis hgt : |a─b| > |a─c| (from the by_cases split
   on step1's disjunction) is just repackaged here. -/
theorem helper_1_6_step2 (a b c : Point) (hgt : |(a─b)| > |(a─c)|) :
    |(a─b)| > |(a─c)| := by
  exact hgt

end Elements.Book1
