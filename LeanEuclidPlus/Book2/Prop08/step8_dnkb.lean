import SystemE
import Book2.Prop08.step8_dnkb_dfbl
import Book2.Prop08.step8_dnkb_abmn
import Book2.Prop08.step8_dnkb_koffdf
import Book2.Prop08.step8_dnkb_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

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
  have step8_dnkb_dfbl : ¬(DF.intersectsLine BL) := by euclid_apply (helper_2_8_step8_dnkb_dfbl a b d e f AB AE BL DF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)))
  have step8_dnkb_abmn : ¬(AB.intersectsLine MN) := by euclid_apply (helper_2_8_step8_dnkb_abmn AB MN (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)))
  have step8_dnkb_koffdf : ¬(k.onLine DF) := by euclid_apply (helper_2_8_step8_dnkb_koffdf a b d f k AB BL DF (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show ¬(DF.intersectsLine BL); assumption)))
  have step8_dnkb_ss : d.sameSide b MN := by euclid_apply (helper_2_8_step8_dnkb_ss a b d e k AB AE BL ED MN (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine MN); assumption)))
  have h_n_ne_k : n ≠ k := by
    intro hnk
    exact step8_dnkb_koffdf (hnk ▸ h_n_df)
  euclid_finish

end Elements.Book2
