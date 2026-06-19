import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.8 sub: |(k─l)| = |(a─c)|. Rectangle AL = formParallelogram k l a c KM AB AK CE; opposite
   sides are equal (proposition_34'): with (a,b,c,d) = (k,l,a,c) the first conjunct |a─b| = |c─d|
   reads |k─l| = |a─c|. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_bases (a c k l : Point) (KM AB AK CE : Line)
    (halpar : formParallelogram k l a c KM AB AK CE) :
    |(k─l)| = |(a─c)| := by
  euclid_apply (Elements.Book1.proposition_34' k l a c KM AB AK CE)
  euclid_finish

end Elements.Book2
