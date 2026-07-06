import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step6_d_side_par
    (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_h_AD : h.onLine AD)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_g_BC : g.onLine BC)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_e_AB : e.onLine AB)
    (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD) (h_f_CD : f.onLine CD)
    (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC) (h_k_AC : k.onLine AC)
    (h_e_EF : e.onLine EF) (h_k_EF : k.onLine EF) (h_f_EF : f.onLine EF)
    (h_h_GH : h.onLine GH) (h_k_GH : k.onLine GH) (h_g_GH : g.onLine GH)
    (h_dc : d ≠ c) (h_ac : a ≠ c) (h_hk : h ≠ k) (h_fc : f ≠ c)
    (h_sameSide_aeGH : a.sameSide e GH)
    (h_par_AD_BC : ¬AD.intersectsLine BC) (h_par_AB_CD : ¬AB.intersectsLine CD)
    (h_par_AD_EF : ¬AD.intersectsLine EF) (h_par_AB_GH : ¬AB.intersectsLine GH)
    (h_par_EF_BC : ¬EF.intersectsLine BC) (h_par_GH_CD : ¬GH.intersectsLine CD)
    (h_betw_ahd : between a h d)
    : formParallelogram h d k f AD EF GH CD := by
  euclid_finish

end Elements.Book1
