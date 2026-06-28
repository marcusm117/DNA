import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_11_step8_eb
    (a b c e f f0 : Point)
    (hbet_aec : between a e c)
    (hbet_caf0 : between c a f0)
    (hbet_eff0 : between e f f0)
    (hef_be : |(e─f)| = |(b─e)|) :
    |(e─b)| = |(a─e)| + |(a─f)| := by
  have hbet_eaf : between e a f := by euclid_finish
  euclid_finish

end Elements.Book2
