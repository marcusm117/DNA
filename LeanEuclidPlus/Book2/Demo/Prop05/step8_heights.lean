import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.8 sub: |(k─a)| = |(c─l)|. Rectangle AL = formParallelogram k l a c KM AB AK CE; opposite
   sides are equal (proposition_34'): with (a,b,c,d) = (k,l,a,c) the second conjunct |a─c| = |b─d|
   reads |k─a| = |l─c| = |c─l|. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_heights (a c k l : Point) (KM AB AK CE : Line)
    (halpar : formParallelogram k l a c KM AB AK CE) :
    |(k─a)| = |(c─l)| := by
  euclid_apply (Elements.Book1.proposition_34' k l a c KM AB AK CE)
  euclid_finish

end Elements.Book2
