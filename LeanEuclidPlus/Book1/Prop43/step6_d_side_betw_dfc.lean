import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step6_d_side_betw_dfc
    (a c d f h k : Point) (AD EF CD AC GH : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_h_AD : h.onLine AD)
    (h_k_EF : k.onLine EF) (h_f_EF : f.onLine EF)
    (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD) (h_f_CD : f.onLine CD)
    (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC) (h_k_AC : k.onLine AC)
    (h_h_GH : h.onLine GH) (h_k_GH : k.onLine GH)
    (h_dc : d ≠ c) (h_hk : h ≠ k)
    (h_betw_ahd : between a h d)
    (h_par_AD_EF : ¬AD.intersectsLine EF)
    (h_par_GH_CD : ¬GH.intersectsLine CD)
    : between d f c := by
  euclid_finish

end Elements.Book1
