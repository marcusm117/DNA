import SystemE
import Helpers.Area
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step20_ak (a b c d e g k m q : Point)
    (AB AE BL CH ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_chbl : ¬(CH.intersectsLine BL))
    (h_qkd : between q k d)
    (h_cbgk : formParallelogram c b g k AB MN CH BL) :
    Triangle.area △ a:b:k + Triangle.area △ a:k:m =
      (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) := by
  have step20_akpar : formParallelogram a b m k AB MN AE BL := by sorry
  have step20_mgk : between m g k := by sorry
  euclid_apply (sum_parallelograms_area a b m k c g AB MN AE BL)
  euclid_apply (Elements.parallelogram_area' c b g k AB MN CH BL)
  euclid_finish

end Elements.Book2
