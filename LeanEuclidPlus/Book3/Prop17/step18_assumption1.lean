import SystemE
import Book3.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step18_assumption1 : ∀ (p q r : Point) (γ : Circle) (L : Line),
    r.isCentre γ ∧ p.onCircle γ ∧ distinctPointsOnLine p q L ∧ ∠ r:p:q = ∟ →
    (∃ s : Point, s.onLine L ∧ s.onCircle γ) ∧ ¬ L.intersectsCircle γ := by
  intro p q r γ L ⟨hr_cen, hp_on, hdpq, h_angle⟩
  have hr_inside : r.insideCircle γ := center_inside_circle r γ hr_cen
  have hp_ne_r : p ≠ r := by
    intro heq
    exact absurd (point_in_circle_onlyif r r r γ ⟨hr_cen, heq ▸ hp_on, hr_inside⟩) (lt_irrefl _)
  obtain ⟨PR, hp_onPR, hr_onPR⟩ := line_from_points p r hp_ne_r
  obtain ⟨b_ant, hb_ant_onγ, hb_ant_onPR, hbetween_batrp⟩ :=
    intersection_circle_line_extending_points γ PR r p
      ⟨hr_inside, hr_onPR, hp_onPR, hp_ne_r.symm⟩
  have hbetween_prb := (between_symm b_ant r p hbetween_batrp).1
  have h_prb_sym := between_symm p r b_ant hbetween_prb
  have h_eq_angles : ∠r:p:q = ∠b_ant:p:q :=
    equal_angles p r b_ant q q PR L
      ⟨hp_onPR, hr_onPR, hb_ant_onPR, hdpq.1, hdpq.2.1, hdpq.2.1,
       hp_ne_r.symm, h_prb_sym.2.2.1.symm, hdpq.2.2.symm, hdpq.2.2.symm,
       h_prb_sym.2.2.2, fun h => absurd rfl (between_symm q p q h).2.2.1⟩
  have h_conv_angle : ∠q:p:b_ant = ∟ :=
    (angle_symm q p b_ant ⟨hdpq.2.2.symm, h_prb_sym.2.2.1⟩).trans
      (h_eq_angles.symm.trans h_angle)
  exact (proposition_16 p b_ant r q γ L
    ⟨hr_cen, hp_on, hb_ant_onγ, hbetween_prb, hdpq, h_conv_angle⟩).1

end Elements.Book3
