import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_hgNd (ABC : Circle) (a b c d e f g : Point) (AB DC : Line)
    (h_a_on : a.onCircle ABC) (h_b_on : b.onCircle ABC)
    (h_c_on : c.onCircle ABC) (h_e_on : e.onCircle ABC)
    (h_bet_adb : between a d b)
    (h_bet_cde : between c d e)
    (h_bet_cfe : between c f e) (h_bisect_cf : |(c─f)| = |(f─e)|)
    (h_a_on_AB : a.onLine AB) (h_b_on_AB : b.onLine AB)
    (h_d_on_DC : d.onLine DC) (h_c_on_DC : c.onLine DC) (h_e_on_DC : e.onLine DC)
    (h_g_center : g.isCentre ABC) (h_gNf : f ≠ g) :
    g ≠ d := by
  by_cases h_gon : g.onLine AB
  · intro h_eq
    have h_cge : between c g e := h_eq ▸ h_bet_cde
    have h_g_on_DC : g.onLine DC := h_eq ▸ h_d_on_DC
    have h_rad_ce : |(g─e)| = |(g─c)| :=
      point_on_circle_onlyif g c e ABC ⟨h_g_center, h_c_on, h_e_on⟩
    have h_len_cge : |(c─g)| + |(g─e)| = |(c─e)| := between_if c g e h_cge
    have h_len_cfe : |(c─f)| + |(f─e)| = |(c─e)| := between_if c f e h_bet_cfe
    have h_f_on_DC : f.onLine DC :=
      between_same_line_in c f e DC ⟨h_bet_cfe, h_c_on_DC, h_e_on_DC⟩
    euclid_finish
  · intro h_eq
    have h_d_on_AB : d.onLine AB :=
      between_same_line_in a d b AB ⟨h_bet_adb, h_a_on_AB, h_b_on_AB⟩
    exact h_gon (h_eq ▸ h_d_on_AB)

end Elements.Book3
