import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.13 sub: area(LHGE) = |l─e| · |l─h|. LHGE is the square LG (formParallelogram l e h g CE BG KM EF)
   with the right angle ∠ l:h:g = ∟, so rectangle_area gives △l:h:g + △l:e:g = |l─e|·|l─h|;
   △l:g:h = △l:h:g by permutation. -/
theorem helper_2_6_step13_rect (e g h l : Point) (CE EF KM BG : Line)
    (hpar : formParallelogram l e h g CE BG KM EF)
    (hlhg : ∠ l:h:g = ∟) :
    Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(l─e)| * |(l─h)| := by
  euclid_intros
  euclid_apply (rectangle_area l e h g CE BG KM EF)
  euclid_finish

end Elements.Book2
