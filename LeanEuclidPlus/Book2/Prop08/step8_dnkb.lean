import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step8_dnkb (a b d e f k n : Point)
    (AB AE BL DF ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_k_mn : k.onLine MN) (h_n_mn : n.onLine MN) (h_n_df : n.onLine DF)
    (h_bl_ae : ¬(BL.intersectsLine AE)) (h_mn_ab : ¬(MN.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF))
    (h_dae : ∠ d:a:e = ∟) (h_adf : ∠ a:d:f = ∟) :
    formParallelogram d n b k DF BL AB MN := by
  have step8_dnkb_dfbl : ¬(DF.intersectsLine BL) := by sorry
  have step8_dnkb_abmn : ¬(AB.intersectsLine MN) := by sorry
  have step8_dnkb_koffdf : ¬(k.onLine DF) := by sorry
  have step8_dnkb_ss : d.sameSide b MN := by sorry
  have h_n_ne_k : n ≠ k := by
    intro hnk
    exact step8_dnkb_koffdf (hnk ▸ h_n_df)
  euclid_finish

end Elements.Book2
