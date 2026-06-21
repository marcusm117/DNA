import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.15 sub: area(CEFD) = |c─d|·|c─d|. CEFD is the square (formParallelogram c d e f AB EF CE DF) with
   the right angle ∠ c:e:f = ∟, so rectangle_area gives △c:e:f + △c:d:f = |c─d|·|c─e|; △c:d:f = △c:f:d
   by permutation and |c─e| = |c─d| (square side). Hence △c:e:f + △c:f:d = |c─d|·|c─d|. -/
theorem helper_2_6_step15_sq (c d e f : Point) (AB EF CE DF : Line)
    (hpar : formParallelogram c d e f AB EF CE DF)
    (hcef : ∠ c:e:f = ∟) (hce_cd : |(c─e)| = |(c─d)|) :
    Triangle.area △ c:e:f + Triangle.area △ c:f:d = |(c─d)| * |(c─d)| := by
  euclid_intros
  euclid_apply (rectangle_area c d e f AB EF CE DF)
  euclid_finish

end Elements.Book2
