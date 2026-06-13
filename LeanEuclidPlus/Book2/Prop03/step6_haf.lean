import SystemE
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

/- sub-fact for 2.3.6: |a─f| = |c─d|. AF and CD are opposite sides of the parallelogram ACDF, hence
   equal (proposition_34': for formParallelogram a c f d, |a─f| = |c─d|). -/
set_option systemE.solverTime 30 in
theorem helper_2_step6_haf (a c d f : Point) (AB DE CD AF : Line)
    (hpar : formParallelogram a c f d AB DE AF CD) :
    |(a─f)| = |(c─d)| := by
  euclid_intros
  euclid_apply (proposition_34' a c f d AB DE AF CD)
  euclid_finish

end Elements.Book2
