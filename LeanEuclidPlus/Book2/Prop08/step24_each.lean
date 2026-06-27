import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step24_each (a b c d e : Point)
    (AB AE CH : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH)
    (h_ch_ae : ¬(CH.intersectsLine AE))
    (h_dae : ∠ d:a:e = ∟) :
    e.sameSide a CH := by
  have h_a_off_ch : ¬(a.onLine CH) := by
    euclid_finish
  have hne_ch_ae : CH ≠ AE := fun heq => h_a_off_ch (heq ▸ h_a_ae)
  euclid_apply (Elements.sameSide_of_parallel_both e a AE CH)
  euclid_finish

end Elements.Book2
