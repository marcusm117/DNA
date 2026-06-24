import SystemE
import Book.Prop34
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step12 (a b c d e f g k q n : Point)
    (AB AE BL CH DF ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_n_mn : n.onLine MN)
    (h_n_df : n.onLine DF)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_ae_df : ¬(AE.intersectsLine DF))
    (h_dae : ∠ d:a:e = ∟) (h_adf : ∠ a:d:f = ∟)
    (h_bd_eq : |(b─d)| = |(c─b)|) :
    |(c─g)| = |(g─q)| := by
  have step12_cbgk : formParallelogram c b g k AB MN CH BL := by sorry
  have step12_bdbk : |(b─d)| = |(b─k)| := by sorry
  have step12_gkgq : |(g─k)| = |(g─q)| := by sorry
  euclid_apply (line_from_points b g) as BG
  euclid_apply (Elements.Book1.proposition_34 c b g k AB MN CH BL BG)
  have hcg_bk : |(c─g)| = |(b─k)| := by
    euclid_finish
  have hcb_gk : |(c─b)| = |(g─k)| := by
    euclid_finish
  linarith

end Elements.Book2
