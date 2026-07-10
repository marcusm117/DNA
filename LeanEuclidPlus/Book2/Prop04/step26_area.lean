import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.26 sub: area(ACGH) = |a─c|·|a─h| via rectangle_area on the parallelogram ACGH
   (formParallelogram a c h g) with the right angle ∠ a:h:g = ∟. -/
theorem helper_2_4_step26_area (a c h g : Point) (AB HK AD CF : Line)
    (hpar : formParallelogram a c h g AB HK AD CF)
    (hahg : ∠ a:h:g = ∟) :
    Triangle.area △ a:h:g + Triangle.area △ a:g:c = |(a─c)| * |(a─h)| := by
  euclid_intros
  euclid_apply (rectangle_area a c h g AB HK AD CF)
  euclid_finish

end Elements.Book2
