import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step16 (ABC : Circle) (a b c d e f g : Point) (AB DC GD : Line)
    (h_a_on_AB : a.onLine AB) (h_b_on_AB : b.onLine AB)
    (h_c_on_DC : c.onLine DC) (h_e_on_DC : e.onLine DC) (h_d_on_DC : d.onLine DC)
    (h_g_on_GD : g.onLine GD) (h_d_on_GD : d.onLine GD)
    (h_bet_adb : between a d b)
    (h_bet_cde : between c d e)
    (h_bet_cfe : between c f e)
    (h_cf_fe : |(c─f)| = |(f─e)|)
    (h_adc_perp : ∠ a:d:c = ∟)
    (h_g_center : g.isCentre ABC)
    (h_c_on_circle : c.onCircle ABC)
    (h_e_on_circle : e.onCircle ABC)
    (h_step9 : |(a─d)| = |(b─d)| ∧ |(d─g)| = |(d─g)|)
    (h_step10 : |(g─a)| = |(g─b)|)
    (h_step12 : ∠ a:d:g = ∟ ∧ ∠ g:d:b = ∟)
    (h_ne_fg : f ≠ g)
    (h_gNd : g ≠ d) :
    False := by
  have h_gc_ge : |(g─c)| = |(g─e)| :=
    (point_on_circle_onlyif g c e ABC ⟨h_g_center, h_c_on_circle, h_e_on_circle⟩).symm
  have h_adg_perp : ∠ a:d:g = ∟ := h_step12.1
  have h_ad_db := h_step9.1
  have h_d_on_AB : d.onLine AB :=
    between_same_line_in a d b AB ⟨h_bet_adb, h_a_on_AB, h_b_on_AB⟩
  have h_f_on_DC : f.onLine DC :=
    between_same_line_in c f e DC ⟨h_bet_cfe, h_c_on_DC, h_e_on_DC⟩
  have h_cNd : c ≠ d := (between_symm c d e h_bet_cde).2.1
  have h_aNd : a ≠ d := (between_symm a d b h_bet_adb).2.1
  euclid_finish

end Elements.Book3
