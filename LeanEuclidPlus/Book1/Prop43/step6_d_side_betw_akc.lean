import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step6_d_side_betw_akc
    (a c d h k : Point) (AD GH CD AC : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_h_AD : h.onLine AD)
    (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC) (h_k_AC : k.onLine AC)
    (h_h_GH : h.onLine GH) (h_k_GH : k.onLine GH)
    (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD)
    (h_ac : a ≠ c) (h_hk : h ≠ k)
    (h_betw_ahd : between a h d)
    (h_par_GH_CD : ¬GH.intersectsLine CD)
    : between a k c := by
  euclid_finish

end Elements.Book1
