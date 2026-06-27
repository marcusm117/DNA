import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- between d n f : n = MN ∩ DF lies between d and f on DF. MN separates d (on AB)
   from f (on EF); the diagonal ED crosses MN at k, and EF∥MN (h_efmn) puts f on
   e's side. Mirror of `between a m e` on the DF side. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_dnf (a b c d e f k n q : Point)
    (AB AE DF EF ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF) (h_n_df : n.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_k_mn : k.onLine MN) (h_n_mn : n.onLine MN)
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_efmn : ¬(MN.intersectsLine EF)) (h_dae : ∠ d:a:e = ∟)
    (h_qkd : between q k d) (h_kqe : between k q e) :
    between d n f := by
  have h_e_off_ab : ¬(e.onLine AB) := by
    euclid_apply (Elements.offLine_of_right_angle a d e AB)
    euclid_finish
  have h_k_off_ab : ¬(k.onLine AB) := by
    euclid_finish
  have hne_mn_ab : MN ≠ AB := fun heq => h_k_off_ab (heq ▸ h_k_mn)
  have h_ekd : between e k d := by
    euclid_finish
  have h_ad_mn : a.sameSide d MN := by
    euclid_apply (Elements.sameSide_of_parallel_both a d AB MN)
    euclid_finish
  euclid_apply (pasch_3 e k d MN)
  have h_df_opp : ¬(d.sameSide f MN) := by
    euclid_finish
  euclid_apply (pasch_4 d n f MN DF)
  euclid_finish

end Elements.Book2
