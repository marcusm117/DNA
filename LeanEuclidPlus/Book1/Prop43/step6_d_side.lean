import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step6_d_side
    (a c d e f h k : Point) (AD EF GH CD AC AB : Line)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_h_AD : h.onLine AD)
    (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC) (h_k_AC : k.onLine AC)
    (h_k_EF : k.onLine EF) (h_f_EF : f.onLine EF)
    (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD) (h_f_CD : f.onLine CD)
    (h_h_GH : h.onLine GH) (h_k_GH : k.onLine GH)
    (h_a_AB : a.onLine AB) (h_e_AB : e.onLine AB)
    (h_ac : a ≠ c) (h_dc : d ≠ c) (h_hk : h ≠ k) (h_fc : f ≠ c)
    (h_sameSide_aeGH : a.sameSide e GH)
    (h_par_AD_EF : ¬AD.intersectsLine EF)
    (h_par_GH_CD : ¬GH.intersectsLine CD)
    (h_par_AB_GH : ¬AB.intersectsLine GH)
    (h_par_AB_CD : ¬AB.intersectsLine CD)
    (h_betw_ahd : between a h d)
    (h_betw_akc : between a k c)
    (h_betw_dfc : between d f c)
    (step6_d_side_par : formParallelogram h d k f AD EF GH CD)
    : Triangle.area △ a:h:k + Triangle.area △ k:f:c +
      Triangle.area △ h:k:f + Triangle.area △ h:f:d = Triangle.area △ a:d:c := by
  euclid_apply (sum_areas_if a c k d AC)
  euclid_apply (sum_areas_if a d h k AD)
  euclid_apply (sum_areas_if d c f k CD)
  euclid_apply (parallelogram_area h d k f AD EF GH CD)
  have h_sym1 : Triangle.area △ d:h:k = Triangle.area △ k:h:d :=
    (area_symm_1 d h k).trans (area_symm_2 k d h)
  have h_sym2 : Triangle.area △ d:k:f = Triangle.area △ d:f:k := area_symm_2 d k f
  linarith

end Elements.Book1
