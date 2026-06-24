import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step12_gkgq_ang_gsaed (a b c d e g k q : Point) (AB AE BL CH ED MN : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_dae : ∠ d:a:e = ∟)
    (h_triade : formTriangle a d e AB ED AE)
    (h_trigkq : formTriangle g k q MN ED CH) :
    g.sameSide a ED := by
  euclid_finish

end Elements.Book2
