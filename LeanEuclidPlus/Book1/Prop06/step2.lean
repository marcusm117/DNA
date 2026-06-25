import SystemE

namespace Elements.Book1

/- 1.6.2: Let AB be greater. The case hypothesis hgt : |a─b| > |a─c| (from the by_cases split
   on step1's disjunction) is just repackaged here. -/
set_option systemE.solverTime 30 in
theorem helper_1_6_step2 (a b c : Point) (hgt : |(a─b)| > |(a─c)|) :
    |(a─b)| > |(a─c)| := by
  exact hgt

end Elements.Book1
