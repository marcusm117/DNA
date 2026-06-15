import SystemE
import Book.Prop43
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.7.3 sub: proposition_43 complement equality. On the square ADEB (formParallelogram b e a d,
   diagonal B-D through g) with inner parallelograms CGFB (`b f c g`) and HGND (`g n h d`),
   proposition_43 gives △c:a:h + △c:h:g = △f:g:n + △f:n:e. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_compl (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d)
    (hbigpar : formParallelogram b e a d BE AD AB DE)
    (hbke : between b f e)
    (hpar1 : formParallelogram b f c g BE CN AB HF)
    (hpar2 : formParallelogram g n h d CN AD HF DE) :
    Triangle.area △ c:a:h + Triangle.area △ c:h:g
      = Triangle.area △ f:g:n + Triangle.area △ f:n:e := by
  euclid_intros
  euclid_apply (proposition_43 b a d e c n h f g BE AD AB DE BD CN HF)
  euclid_finish

end Elements.Book2
