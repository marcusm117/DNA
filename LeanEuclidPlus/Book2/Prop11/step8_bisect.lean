import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step8_bisect
    (a b c e : Point)
    (hbet_aec : between a e c)
    (hae_ec : |(a─e)| = |(e─c)|)
    (hac_ab : |(a─c)| = |(a─b)|) :
    |(a─b)| = |(a─e)| + |(a─e)| := by
  euclid_finish

end Elements.Book2
