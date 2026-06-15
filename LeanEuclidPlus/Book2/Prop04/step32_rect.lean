import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.32 sub: area(ADEB) = |a─b|² in the b:a:d / b:e:d triangulation. rectangle_area on the
   parallelogram ADEB (formParallelogram b e a d) with right angle ∠ b:a:d = ∟ gives
   △b:a:d + △b:e:d = |b─e|·|b─a|; with |b─e| = |a─b| (square side, hbe) and distance symmetry. -/
theorem helper_2_4_step32_rect (a b d e : Point) (BE AD AB DE : Line)
    (hpar : formParallelogram b e a d BE AD AB DE)
    (hbad : ∠ b:a:d = ∟) (hbe : |(b─e)| = |(a─b)|) :
    Triangle.area △ b:a:d + Triangle.area △ b:e:d = |(a─b)| * |(a─b)| := by
  euclid_intros
  have hrect : Triangle.area △ b:a:d + Triangle.area △ b:e:d = |(b─e)| * |(b─a)| := by
    euclid_apply (rectangle_area b e a d BE AD AB DE)
    euclid_finish
  euclid_finish

end Elements.Book2
