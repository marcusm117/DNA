import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.15 sub: area(LEGH) = |l─e| * |l─h|. LEGH is the square LG (formParallelogram l e h g CE DG KM EF:
   l,e on CE; h,g on DG; l,h on KM; e,g on EF) with the right angle ∠ l:h:g = ∟, so rectangle_area
   gives area(△l:h:g + △l:e:g) = |l─e|·|l─h|; area △l:g:h = △l:h:g by permutation. -/
theorem helper_2_5_step15_rect (e g h l : Point) (CE EF KM DG : Line)
    (hpar : formParallelogram l e h g CE DG KM EF)
    (hlhg : ∠ l:h:g = ∟) :
    Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(l─e)| * |(l─h)| := by
  euclid_intros
  euclid_apply (rectangle_area l e h g CE DG KM EF)
  euclid_finish

end Elements.Book2
