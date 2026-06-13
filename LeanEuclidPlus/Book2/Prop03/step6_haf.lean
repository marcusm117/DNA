import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- sub-fact for 2.3.6: |a─f| = |c─d|. AF and CD are opposite sides of the parallelogram ACDF, hence
   equal (proposition_34': for formParallelogram a c f d, |a─f| = |c─d|). -/
theorem helper_2_3_step6_haf (a c d f : Point) (AB DE CD AF : Line)
    (hpar : formParallelogram a c f d AB DE AF CD) :
    |(a─f)| = |(c─d)| := by
  euclid_intros
  euclid_apply (proposition_34' a c f d AB DE AF CD)
  euclid_finish

end Elements.Book2
