import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_38 : ∀ (a b c d e f: Point) (AD BF AB AC DE DF : Line),
  a.onLine AD ∧ d.onLine AD ∧ formTriangle a b c AB BF AC ∧ formTriangle d e f DE BF DF ∧
  ¬(AD.intersectsLine BF) ∧ (between b c f) ∧ (between b e f) ∧ |(b─c)| = |(e─f)| →
  Triangle.area △ a:b:c = Triangle.area △ d:e:f := by
  sorry

end Elements.Book1
