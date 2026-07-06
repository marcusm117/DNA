import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step6_b_side_betw_aeb
    (a b c e g h k : Point) (AB GH EF BC AC : Line)
    (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC) (h_k_AC : k.onLine AC)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_e_AB : e.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_g_BC : g.onLine BC)
    (h_e_EF : e.onLine EF) (h_k_EF : k.onLine EF)
    (h_h_GH : h.onLine GH) (h_k_GH : k.onLine GH) (h_g_GH : g.onLine GH)
    (h_ac : a ≠ c) (h_hk : h ≠ k)
    (h_sameSide_aeGH : a.sameSide e GH)
    (h_sameSide_kgCD : k.sameSide g CD)
    (h_par_AB_GH : ¬AB.intersectsLine GH)
    (h_par_GH_CD : ¬GH.intersectsLine CD)
    (h_par_EF_BC : ¬EF.intersectsLine BC)
    (h_par_AB_CD : ¬AB.intersectsLine CD)
    : between a e b := by
  euclid_finish

end Elements.Book1
