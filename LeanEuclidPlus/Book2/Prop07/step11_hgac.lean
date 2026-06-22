import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.7.11 sub: |(a─c)| = |(h─g)|. In the rectangle ACGH (formParallelogram a c h g AB HF AD CN)
   the opposite sides AC and HG are equal [Prop.~1.34']. -/
theorem helper_2_7_step11_hgac (a c h g : Point) (AB HF AD CN : Line)
    (hpar : formParallelogram a c h g AB HF AD CN) :
    |(a─c)| = |(h─g)| := by
  euclid_intros
  euclid_apply (proposition_34' a c h g AB HF AD CN)
  euclid_finish

end Elements.Book2
