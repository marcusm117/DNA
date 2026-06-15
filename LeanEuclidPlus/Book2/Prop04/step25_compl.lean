import SystemE
import Book.Prop43
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.25 sub: proposition_43 complement equality. On the square ADEB (formParallelogram b e a d,
   diagonal B-D through g) with inner parallelograms CGKB (`b k c g`) and HGFD (`g f h d`),
   proposition_43 gives △c:a:h + △c:h:g = △k:g:f + △k:f:e. -/
theorem helper_2_4_step25_compl (a b c d e f g h k : Point) (AB CF AD BE HK BD DE : Line)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d)
    (hbigpar : formParallelogram b e a d BE AD AB DE)
    (hbke : between b k e)
    (hpar1 : formParallelogram b k c g BE CF AB HK)
    (hpar2 : formParallelogram g f h d CF AD HK DE) :
    Triangle.area △ c:a:h + Triangle.area △ c:h:g
      = Triangle.area △ k:g:f + Triangle.area △ k:f:e := by
  euclid_intros
  euclid_apply (proposition_43 b a d e c f h k g BE AD AB DE BD CF HK)
  euclid_finish

end Elements.Book2
