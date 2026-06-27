import SystemE
import Book.Prop34
import Helpers.Area
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step21 (a b c d e g k m q : Point)
    (AB AE BL CH ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) :
    Triangle.area △ a:b:k + Triangle.area △ a:k:m = |(a─b)| * |(b─d)| := by
  have step12_gkgq_ang_qkd : between q k d := by sorry
  have step12_gkgq_ang_kqe : between k q e := by sorry
  have step20_akpar : formParallelogram a b m k AB MN AE BL := by sorry
  have step12_bdbk : |(b─d)| = |(b─k)| := by sorry
  have step21_ame : between a m e := by sorry
  have step21_amk : ∠ a:m:k = ∟ := by sorry
  euclid_apply (line_from_points b m) as BM
  euclid_apply (Elements.Book1.proposition_34 a b m k AB MN AE BL BM)
  euclid_apply (rectangle_area a b m k AB MN AE BL)
  euclid_finish

end Elements.Book2
