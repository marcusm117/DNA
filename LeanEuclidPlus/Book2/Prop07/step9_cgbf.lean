import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.7.9 sub: |(c─g)| = |(b─f)|. In the parallelogram CBFG (formParallelogram c b g f AB HF CN BE),
   opposite sides CG and BF are equal [Prop.~1.34]. -/
theorem helper_2_7_step9_cgbf (c b g f : Point) (AB HF CN BE BD : Line)
    (hpar : formParallelogram c b g f AB HF CN BE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hbg : b ≠ g) :
    |(c─g)| = |(b─f)| := by
  euclid_intros
  euclid_apply (proposition_34 c b g f AB HF CN BE BD)
  euclid_finish

end Elements.Book2
