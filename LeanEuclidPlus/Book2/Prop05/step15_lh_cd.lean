import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.15 sub: |l─h| = |c─d|. CDHL is a parallelogram (formParallelogram c d l h AB KM CE DG:
   c,d on AB; l,h on KM; c,l on CE; d,h on DG), so opposite sides CD and LH are equal [Prop.~1.34],
   giving |c─d| = |l─h|. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step15_lh_cd (c d h l : Point) (AB KM CE DG : Line)
    (hpar : formParallelogram c d l h AB KM CE DG) :
    |(l─h)| = |(c─d)| := by
  euclid_intros
  euclid_apply (proposition_34' c d l h AB KM CE DG)
  euclid_finish

end Elements.Book2
