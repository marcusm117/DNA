import SystemE
import Helpers.Area
import Book2.Prop08.step20_akpar
import Book2.Prop08.step20_mgk
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

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
  have step20_akpar : formParallelogram a b m k AB MN AE BL := by euclid_apply (helper_2_8_step20_akpar a b c d e k m q AB AE BL CH ED MN (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show m.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show between q k d; assumption)))
  have step20_mgk : between m g k := by euclid_apply (helper_2_8_step20_mgk a b c d e g k m AB AE BL CH MN (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show m.onLine AE; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine BL); assumption)))
  euclid_apply (sum_parallelograms_area a b m k c g AB MN AE BL)
  euclid_apply (Elements.parallelogram_area' c b g k AB MN CH BL)
  euclid_finish

end Elements.Book2
