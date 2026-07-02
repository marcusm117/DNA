import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_14_step7 (a b c d e : Point) (AB BC BD : Line)
  (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab_ne : a ≠ b)
  (hb_bc : b.onLine BC) (hc_bc : c.onLine BC) (hbc_ne : b ≠ c)
  (hb_bd : b.onLine BD) (hd_bd : d.onLine BD) (hbd_ne : b ≠ d)
  (hc_ab : ¬c.onLine AB) (hd_ab : ¬d.onLine AB) (hcd_ab : ¬c.sameSide d AB)
  (hne : BC ≠ BD)
  (he_bc : e.onLine BC) (hcbe : between c b e)
  (h2 : ∠ a:b:c + ∠ a:b:e = ∟ + ∟)
  (h6 : ∠ a:b:e = ∠ a:b:d)
  : False := by
  by_cases hcase : a.sameSide e BD
  · euclid_apply (sum_angles_onlyif b a d e AB BD)
    euclid_finish
  · euclid_apply (sum_angles_onlyif b a e d AB BC)
    euclid_finish

end Elements.Book1
