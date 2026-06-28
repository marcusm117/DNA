import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_11_step8
    (a b c e f f0 h : Point) (AB AC AH : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hbet_aec : between a e c)
    (hae_ec : |(a─e)| = |(e─c)|)
    (hac_ab : |(a─c)| = |(a─b)|)
    (hang_bac : ∠ b:a:c = ∟)
    (hbet_caf0 : between c a f0)
    (hbet_eff0 : between e f f0)
    (hef_be : |(e─f)| = |(b─e)|)
    (hah_af : |(a─h)| = |(a─f)|)
    (hhAH : h.onLine AH) (haAH : a.onLine AH)
    (hang_fah : ∠ f:a:h = ∟) :
    |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| := by
  have step8_bisect : |(a─b)| = |(a─e)| + |(a─e)| := by sorry
  have step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by sorry
  have step8_eb : |(e─b)| = |(a─e)| + |(a─f)| := by sorry
  have step8_ahb : |(a─b)| = |(a─h)| + |(b─h)| := by sorry
  have step8_golden : |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| := by sorry
  exact step8_golden

end Elements.Book2
