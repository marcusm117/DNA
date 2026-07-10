import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.13 sub: |c─l| = |b─h|. CBHL is a parallelogram (formParallelogram c b l h AB KM CE BG), so the
   other pair of opposite sides CL and BH are equal [Prop.~1.34]. -/
theorem helper_2_6_step13_cl_bh (b c h l : Point) (AB KM CE BG : Line)
    (hpar : formParallelogram c b l h AB KM CE BG) :
    |(c─l)| = |(b─h)| := by
  euclid_intros
  euclid_apply (proposition_34' c b l h AB KM CE BG)
  euclid_finish

end Elements.Book2
