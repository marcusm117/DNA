import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Upper region formParallelogram m e n f (m-e on AE, n-f on DF, m-n on MN, e-f on EF).
   Used by step26_sq2. Needs AE∥DF (h_ae_df), MN∥EF (h_efmn). -/
theorem helper_2_8_step26_sq2_par (a b c d e f m n : Point)
    (AB AE DF EF MN ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF) (h_n_df : n.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF)
    (h_m_mn : m.onLine MN) (h_n_mn : n.onLine MN)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_ame : between a m e)
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_ef_ab : ¬(EF.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_efmn : ¬(MN.intersectsLine EF))
    (h_dae : ∠ d:a:e = ∟) :
    formParallelogram m e n f AE DF MN EF := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_m_off_ef : ¬(m.onLine EF) := by
    euclid_finish
  have hne_mn_ef : MN ≠ EF := fun heq => h_m_off_ef (heq ▸ h_m_mn)
  have h_mn_ef : m.sameSide n EF := by
    euclid_apply (Elements.sameSide_of_parallel_both m n MN EF)
    euclid_finish
  euclid_finish

end Elements.Book2
