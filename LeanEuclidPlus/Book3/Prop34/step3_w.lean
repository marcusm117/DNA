import SystemE
import Book1.Prop10.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_34_step3_w (b c e f : Point) (ABC : Circle) (BC EF : Line)
    (hb_ABC : b.onCircle ABC) (hc_ABC : c.onCircle ABC)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hbc_ne : b ≠ c)
    (he_EF : e.onLine EF) (hb_EF : b.onLine EF) (hbet_ebf : between e b f)
    (hBC_int : BC.intersectsCircle ABC) (hEF_notint : ¬ EF.intersectsCircle ABC) :
    ∃ w : Point, w.onCircle ABC ∧ w.opposingSides e BC := by
  have hBCneEF : BC ≠ EF := by euclid_finish
  have heb : e ≠ b := by euclid_finish
  -- midpoint m of chord bc lies inside the circle
  euclid_apply (proposition_10 b c BC) as m
  euclid_apply (circle_points_between b c m ABC)
  -- e is off the chord line BC (EF ∩ BC = {b}, e ≠ b)
  have he_off : ¬ e.onLine BC := by euclid_finish
  -- draw e–m and extend through interior m to the far side of BC
  euclid_apply (line_from_points e m) as EM
  euclid_apply (intersection_circle_line_extending_points ABC EM m e) as w
  have hEMneBC : EM ≠ BC := by euclid_finish
  have hw_off : ¬ w.onLine BC := by euclid_finish
  exact ⟨w, by euclid_finish, by euclid_finish⟩

end Elements.Book3
