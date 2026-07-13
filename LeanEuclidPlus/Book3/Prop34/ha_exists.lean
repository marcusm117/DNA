import SystemE
import Book1.Prop10.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_34_ha_exists (b c e f : Point) (ABC : Circle) (BC EF : Line)
    (hb_ABC : b.onCircle ABC) (hc_ABC : c.onCircle ABC)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hbc_ne : b ≠ c)
    (hf_EF : f.onLine EF) (hb_EF : b.onLine EF) (hbet_ebf : between e b f)
    (hBC_int : BC.intersectsCircle ABC) (hEF_notint : ¬ EF.intersectsCircle ABC) :
    ∃ a : Point, a.onCircle ABC ∧ a.opposingSides f BC := by
  have hBCneEF : BC ≠ EF := by euclid_finish
  have hfb : f ≠ b := by euclid_finish
  -- midpoint m of chord bc lies inside the circle
  euclid_apply (proposition_10 b c BC) as m
  euclid_apply (circle_points_between b c m ABC)
  -- f is off the chord line BC (EF ∩ BC = {b}, f ≠ b)
  have hf_off : ¬ f.onLine BC := by euclid_finish
  -- draw f–m and extend through interior m to the far side of BC
  euclid_apply (line_from_points f m) as FM
  euclid_apply (intersection_circle_line_extending_points ABC FM m f) as a
  have hFMneBC : FM ≠ BC := by euclid_finish
  -- a is off BC (FM ∩ BC = {m}, a on circle so a ≠ m)
  have ha_off : ¬ a.onLine BC := by euclid_finish
  exact ⟨a, by euclid_finish, by euclid_finish⟩

end Elements.Book3
