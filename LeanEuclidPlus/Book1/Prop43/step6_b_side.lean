import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step6_b_side
    (a b c e g h k : Point) (AB GH EF BC AC AD CD : Line)
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
    (h_betw_akc : between a k c)
    (h_betw_bgc : between b g c)
    (h_betw_aeb : between a e b)
    -- inner EBG parallelogram sub-node
    (step6_b_side_par : formParallelogram e b k g AB GH EF BC)
    : Triangle.area △ a:e:k + Triangle.area △ k:g:c +
      Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ a:b:c := by
  euclid_apply (sum_areas_if a c k b AC)
  euclid_apply (sum_areas_if a b e k AB)
  euclid_apply (sum_areas_if b c g k BC)
  euclid_apply (parallelogram_area e b k g AB GH EF BC)
  have h_sym1 : Triangle.area △ k:e:b = Triangle.area △ b:e:k :=
    (area_symm_1 k e b).trans (area_symm_2 b k e)
  have h_sym2 : Triangle.area △ b:g:k = Triangle.area △ b:k:g := area_symm_2 b g k
  have h_sym3 : Triangle.area △ e:k:g = Triangle.area △ e:g:k := area_symm_2 e k g
  have h_sym4 : Triangle.area △ e:g:b = Triangle.area △ e:b:g := area_symm_2 e g b
  linarith

end Elements.Book1
