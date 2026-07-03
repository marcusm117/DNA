import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_2_step9 (d a b g l : Point)
    (h1 : |(d─l)| = |(d─g)|) (h2 : |(d─a)| = |(d─b)|)
    (h3 : between l a d) (h4 : between g b d) :
    |(a─l)| = |(b─g)| := by
  euclid_apply (between_if l a d)
  euclid_apply (between_if g b d)
  euclid_finish

end Elements.Book1
