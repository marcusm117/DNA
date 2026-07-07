import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step18 (ABC : Circle) (a b c d e f : Point) (AB DC : Line)
    (h_bNa : b ≠ a)
    (h_a_on_circle : a.onCircle ABC)
    (h_b_on_circle : b.onCircle ABC)
    (h_c_on_circle : c.onCircle ABC)
    (h_e_on_circle : e.onCircle ABC)
    (h_a_on_AB : a.onLine AB) (h_b_on_AB : b.onLine AB)
    (h_c_on_DC : c.onLine DC) (h_e_on_DC : e.onLine DC) (h_d_on_DC : d.onLine DC)
    (h_bet_adb : between a d b)
    (h_bet_cde : between c d e)
    (h_bet_cfe : between c f e)
    (h_ad_db : |(a─d)| = |(d─b)|)
    (h_cf_fe : |(c─f)| = |(f─e)|)
    (h_adc_perp : ∠ a:d:c = ∟) :
    ∀ (g' : Point), g' ≠ f → ¬g'.isCentre ABC := by
  intro g' hne hcenter
  have h_g'c_ge : |(g'─c)| = |(g'─e)| :=
    (point_on_circle_onlyif g' c e ABC ⟨hcenter, h_c_on_circle, h_e_on_circle⟩).symm
  have h_g'a_gb : |(g'─a)| = |(g'─b)| :=
    (point_on_circle_onlyif g' a b ABC ⟨hcenter, h_a_on_circle, h_b_on_circle⟩).symm
  have h_d_on_AB : d.onLine AB :=
    between_same_line_in a d b AB ⟨h_bet_adb, h_a_on_AB, h_b_on_AB⟩
  have h_f_on_DC : f.onLine DC :=
    between_same_line_in c f e DC ⟨h_bet_cfe, h_c_on_DC, h_e_on_DC⟩
  have h_cNd : c ≠ d := (between_symm c d e h_bet_cde).2.1
  have h_aNd : a ≠ d := (between_symm a d b h_bet_adb).2.1
  by_cases hg'd : g' = d
  · -- g' = d: both d and f are midpoints of CE → contradiction
    subst hg'd
    euclid_finish
  · -- g' ≠ d: keep G'D in outer scope so final euclid_finish can use g'.onLine G'D
    have hg'Na : g' ≠ a := by intro heq; subst heq; euclid_finish
    have hg'Nb : g' ≠ b := by intro heq; subst heq; euclid_finish
    obtain ⟨G'D, hg'_on_G'D, hd_on_G'D⟩ := line_from_points g' d hg'd
    have h_adg'_perp : ∠ a:d:g' = ∟ := by
      obtain ⟨G'A, hg'_on_G'A, ha_on_G'A⟩ := line_from_points g' a hg'Na
      obtain ⟨G'B, hg'_on_G'B, hb_on_G'B⟩ := line_from_points g' b hg'Nb
      have h_g'_off_AB : ¬g'.onLine AB := by intro hon; euclid_finish
      have h_eq_angles : ∠ a:d:g' = ∠ g':d:b := by euclid_finish
      exact perpendicular_if a b d g' AB
        ⟨h_a_on_AB, h_b_on_AB, h_bet_adb, h_g'_off_AB, h_eq_angles⟩
    euclid_finish

end Elements.Book3
