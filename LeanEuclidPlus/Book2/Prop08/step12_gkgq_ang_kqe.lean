import SystemE
import Book.Prop30
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

theorem helper_2_8_step12_gkgq_ang_kqe (a b c d e g k q : Point) (AB AE BL CH ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_dae : ∠ d:a:e = ∟) :
    between k q e := by
  have h_a_off_ch : ¬(a.onLine CH) := by
    euclid_finish
  have h_b_off_ae : ¬(b.onLine AE) := by
    euclid_finish
  have h_b_off_ch : ¬(b.onLine CH) := by
    intro hon
    euclid_apply (intersection_lines_common_point b AB CH)
    euclid_finish
  have hne_ch_ae : CH ≠ AE := fun heq => h_a_off_ch (heq ▸ h_a_ae)
  have hne_bl_ae : BL ≠ AE := fun heq => h_b_off_ae (heq ▸ h_b_bl)
  have hne_bl_ch : BL ≠ CH := fun heq => h_b_off_ch (heq ▸ h_b_bl)
  have h_ae_ch : ¬(AE.intersectsLine CH) := by
    euclid_finish
  have h_bl_ch : ¬(BL.intersectsLine CH) := by
    euclid_apply (proposition_30 BL CH AE)
    euclid_finish
  have h_ae_cs : a.sameSide e CH := by
    euclid_apply (Elements.sameSide_of_parallel' a e a AE CH)
    euclid_finish
  have h_bk_cs : b.sameSide k CH := by
    euclid_apply (Elements.sameSide_of_parallel' b k b BL CH)
    euclid_finish
  euclid_apply (pasch_3 a c b CH)
  have h_ke_opp : ¬(k.sameSide e CH) := by
    euclid_finish
  euclid_apply (pasch_4 k q e CH ED)
  euclid_finish

end Elements.Book2
