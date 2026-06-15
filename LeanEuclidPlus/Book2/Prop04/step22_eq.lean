import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.22 sub: HGFD is equilateral. From the parallelogram HGFD (proposition_34'): |h─g| = |f─d| and
   |g─f| = |d─h|. From ACGH (step22_acgh): |a─c| = |h─g| and |a─h| = |c─g|. With |c─g| = |b─c|
   (step8, distance symmetry), |a─d| = |a─h| + |h─d| (a-h-d), |a─b| = |a─c| + |c─b| (a-c-b) and
   |a─d| = |a─b| (square side), the lengths chain to |d─h| = |a─c| = |h─g|, so all sides equal. -/
theorem helper_2_4_step22_eq (a b c d f g h : Point) (HK DE AD CF : Line)
    (hacb : between a c b) (hahd : between a h d)
    (hpar : formParallelogram h g d f HK DE AD CF)
    (hacng : |(a─c)| = |(h─g)|) (hahcg : |(a─h)| = |(c─g)|)
    (hadab : |(a─d)| = |(a─b)|) (hstep8 : |(b─c)| = |(c─g)|) :
    |(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)| := by
  euclid_intros
  euclid_apply (proposition_34' h g d f HK DE AD CF)
  euclid_finish

end Elements.Book2
