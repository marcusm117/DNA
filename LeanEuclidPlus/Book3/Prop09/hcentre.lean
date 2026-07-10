import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop09.hcentre_aonL
import Book3.Prop09.hcentre_bonL
import Book3.Prop09.hcentre_conL
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

/-
  Helper for the two @euclid_gap branches of proposition_9.
  In both branches (e=d and f=d), we have:
    d inside ABC; a,b,c on ABC (distinct); |da|=|db|=|dc|.
  Goal: d.isCentre ABC.

  Proof: get real centre o; build circle alpha0 centred at d through a,b,c;
  if alpha0=ABC done; if alpha0≠ABC and d≠o, use circles_intersections_diff_side
  + pigeon_hole (none-on-L case) or a metric argument (some-on-L cases).
-/
theorem helper_3_9_hcentre
    (ABC : Circle) (a b c d e f : Point) (AB BC : Line)
    (hd_inside : d.insideCircle ABC)
    (ha : a.onCircle ABC) (hb : b.onCircle ABC) (hc : c.onCircle ABC)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_da_db : |(d─a)| = |(d─b)|) (h_db_dc : |(d─b)| = |(d─c)|)
    (hstep1 : distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
              between a e b ∧ |(a─e)| = |(e─b)| ∧ between b f c ∧ |(b─f)| = |(f─c)|) :
    d.isCentre ABC := by
  obtain ⟨⟨ha_AB, hb_AB, _⟩, ⟨hb_BC, hc_BC, _⟩, haeb, hae_eb, hbfc, hbf_fc⟩ := hstep1
  -- get real centre o
  obtain ⟨o, ho⟩ := exists_centre ABC
  by_cases hdo : d = o
  · rw [hdo]; exact ho
  -- d ≠ o: build α₀ centred at d
  have hda : d ≠ a := by euclid_finish
  obtain ⟨α₀, hd_ctr, ha_α₀⟩ := circle_from_points d a hda
  have hb_α₀ : b.onCircle α₀ := by
    apply point_on_circle_if d a b α₀
    exact ⟨hd_ctr, ha_α₀, by linarith⟩
  have hc_α₀ : c.onCircle α₀ := by
    apply point_on_circle_if d a c α₀
    exact ⟨hd_ctr, ha_α₀, by linarith⟩
  by_cases hαABC : α₀ = ABC
  · exact hαABC ▸ hd_ctr
  -- α₀ ≠ ABC and d ≠ o: derive False
  exfalso
  -- line L through d and o
  obtain ⟨L, hd_L, ho_L⟩ := line_from_points d o hdo
  -- pairwise ¬sameSide facts
  have h_ab : ¬(a.sameSide b L) := by
    apply circles_intersections_diff_side d o a b α₀ ABC L
    exact ⟨hαABC, ha_α₀, ha, hb_α₀, hb, hab, hd_ctr, ho, hd_L, ho_L⟩
  have h_ac : ¬(a.sameSide c L) := by
    apply circles_intersections_diff_side d o a c α₀ ABC L
    exact ⟨hαABC, ha_α₀, ha, hc_α₀, hc, hac, hd_ctr, ho, hd_L, ho_L⟩
  have h_bc : ¬(b.sameSide c L) := by
    apply circles_intersections_diff_side d o b c α₀ ABC L
    exact ⟨hαABC, hb_α₀, hb, hc_α₀, hc, hbc, hd_ctr, ho, hd_L, ho_L⟩
  -- case: are any of a, b, c on L?
  by_cases haL : a.onLine L
  · -- a on L: derive False via metric argument (sub-node)
    have hcentre_aonL : False := by euclid_apply (helper_3_9_hcentre_aonL ABC α₀ a b c d e f o AB BC L (by euclid_assumption "" (show d.insideCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)) (by euclid_assumption "" (show |(d─b)| = |(d─c)|; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─b)|; assumption)) (by euclid_assumption "" (show between b f c; assumption)) (by euclid_assumption "" (show |(b─f)| = |(f─c)|; assumption)) (by euclid_assumption "" (show o.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬d = o; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show d.isCentre α₀; assumption)) (by euclid_assumption "" (show a.onCircle α₀; assumption)) (by euclid_assumption "" (show b.onCircle α₀; assumption)) (by euclid_assumption "" (show c.onCircle α₀; assumption)) (by euclid_assumption "" (show ¬α₀ = ABC; assumption)) (by euclid_assumption "" (show d.onLine L; assumption)) (by euclid_assumption "" (show o.onLine L; assumption)) (by euclid_assumption "" (show ¬a.sameSide b L; assumption)) (by euclid_assumption "" (show ¬a.sameSide c L; assumption)) (by euclid_assumption "" (show ¬b.sameSide c L; assumption)) (by euclid_assumption "" (show a.onLine L; assumption)))
    exact hcentre_aonL
  · by_cases hbL : b.onLine L
    · -- b on L: derive False via metric argument (sub-node)
      have hcentre_bonL : False := by euclid_apply (helper_3_9_hcentre_bonL ABC α₀ b c d f o BC L (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show |(d─b)| = |(d─c)|; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show between b f c; assumption)) (by euclid_assumption "" (show |(b─f)| = |(f─c)|; assumption)) (by euclid_assumption "" (show o.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬d = o; assumption)) (by euclid_assumption "" (show d.isCentre α₀; assumption)) (by euclid_assumption "" (show b.onCircle α₀; assumption)) (by euclid_assumption "" (show c.onCircle α₀; assumption)) (by euclid_assumption "" (show d.onLine L; assumption)) (by euclid_assumption "" (show o.onLine L; assumption)) (by euclid_assumption "" (show b.onLine L; assumption)))
      exact hcentre_bonL
    · by_cases hcL : c.onLine L
      · -- c on L: derive False via metric argument (sub-node)
        have hcentre_conL : False := by euclid_apply (helper_3_9_hcentre_conL ABC α₀ b c d f o BC L (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show |(d─b)| = |(d─c)|; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show between b f c; assumption)) (by euclid_assumption "" (show |(b─f)| = |(f─c)|; assumption)) (by euclid_assumption "" (show o.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬d = o; assumption)) (by euclid_assumption "" (show d.isCentre α₀; assumption)) (by euclid_assumption "" (show b.onCircle α₀; assumption)) (by euclid_assumption "" (show c.onCircle α₀; assumption)) (by euclid_assumption "" (show d.onLine L; assumption)) (by euclid_assumption "" (show o.onLine L; assumption)) (by euclid_assumption "" (show ¬b.onLine L; assumption)) (by euclid_assumption "" (show c.onLine L; assumption)))
        exact hcentre_conL
      · -- none on L: pigeon_hole gives two on same side → contradiction
        rcases same_side_pigeon_hole a b c L ⟨haL, hbL, hcL⟩ with h | h | h
        · exact h_ab h
        · exact h_ac h
        · exact h_bc h

end Elements.Book3
