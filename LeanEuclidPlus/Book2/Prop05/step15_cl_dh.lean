import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.15 sub: |c─l| = |d─h|. CDHL is a parallelogram (formParallelogram c d l h AB KM CE DG), so the
   other pair of opposite sides CL and DH are equal [Prop.~1.34]. -/
theorem helper_2_5_step15_cl_dh (c d h l : Point) (AB KM CE DG : Line)
    (hpar : formParallelogram c d l h AB KM CE DG) :
    |(c─l)| = |(d─h)| := by
  euclid_intros
  euclid_apply (proposition_34' c d l h AB KM CE DG)
  euclid_finish

end Elements.Book2
