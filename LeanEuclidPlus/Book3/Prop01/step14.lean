import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step14 (ABC : Circle) (a b c c0 d e f g : Point) (AB DC GD : Line)
    (h_a_on_AB : a.onLine AB) (h_b_on_AB : b.onLine AB)
    (h_c_on_DC : c.onLine DC) (h_e_on_DC : e.onLine DC) (h_d_on_DC : d.onLine DC)
    (h_c0_on_DC : c0.onLine DC) (h_c0_off_AB : ¬c0.onLine AB)
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
    (h_gNd : g ≠ d) :
    ∠ f:d:b = ∟ := by
  have h_d_on_AB : d.onLine AB :=
    between_same_line_in a d b AB ⟨h_bet_adb, h_a_on_AB, h_b_on_AB⟩
  have h_f_on_DC : f.onLine DC :=
    between_same_line_in c f e DC ⟨h_bet_cfe, h_c_on_DC, h_e_on_DC⟩
  have h_cNd : c ≠ d := (between_symm c d e h_bet_cde).2.1
  have h_aNd : a ≠ d := (between_symm a d b h_bet_adb).2.1
  have h_dc_ne_ab : DC ≠ AB := fun h => h_c0_off_AB (h ▸ h_c0_on_DC)
  have h_fNd : f ≠ d := by
    intro h_eq
    -- f = d: d midpoint of CE (|c─d|=|d─e|); g equidistant from c,e (radii);
    -- ∠a:d:g = ∟ (from step12) ⟹ g on perp bisector of CE = line AB;
    -- then g on AB + g≠d + d midpoint of AB ⟹ g=d ⟹ contradiction
    have h_gc_ge : |(g─c)| = |(g─e)| :=
      (point_on_circle_onlyif g c e ABC ⟨h_g_center, h_c_on_circle, h_e_on_circle⟩).symm
    have h_ad_db := h_step9.1
    have h_adg_perp : ∠ a:d:g = ∟ := h_step12.1
    euclid_finish
  have h_f_off_AB : ¬f.onLine AB := fun h_fon =>
    h_dc_ne_ab (two_points_determine_line d f DC AB
      ⟨⟨h_d_on_DC, h_f_on_DC, h_fNd.symm⟩, h_d_on_AB, h_fon⟩)
  by_cases h_bet_cdf : between c d f
  · have h_flat : ∠ c:d:f = ∟ + ∟ := flat_angle_onlyif c d f h_bet_cdf
    euclid_finish
  · have h_equal : ∠ a:d:c = ∠ a:d:f :=
      equal_angles d a a c f AB DC
        ⟨h_d_on_AB, h_a_on_AB, h_a_on_AB, h_d_on_DC, h_c_on_DC, h_f_on_DC,
         h_aNd, h_aNd, h_cNd, h_fNd,
         fun habs => (between_symm a d a habs).2.2.1 rfl,
         h_bet_cdf⟩
    have h_adf_perp : ∠ a:d:f = ∟ := h_equal ▸ h_adc_perp
    euclid_finish

end Elements.Book3
