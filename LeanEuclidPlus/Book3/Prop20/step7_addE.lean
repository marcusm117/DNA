import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step7_addE
  (a b c e f : Point) (BC AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_c_circ : c.onCircle ABC) (h_f_circ : f.onCircle ABC)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_bne_c : b ≠ c)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_bne_a : b ≠ a) (h_cne_a : c ≠ a) (h_aSe : a.sameSide e BC) (h_bet : between f e a)
  (hopp : a.opposingSides f BC)
  : ∠ b:e:c = ∠ b:e:f + ∠ f:e:c := by
  -- F on the opposite side of BC from A ⟹ diameter AEF crosses BC at an interior point x
  euclid_apply (intersection_lines_opposing a f BC AEF)
  have hcross : AEF.intersectsLine BC := by euclid_finish
  euclid_apply (intersection_lines AEF BC) as x
  have hbet_axf : between a x f := by euclid_apply (pasch_4 a x f BC AEF); euclid_finish
  have hx_in : x.insideCircle ABC := by euclid_apply (circle_points_between a f x ABC); euclid_finish
  have hbet_bxc : between b x c := by euclid_apply (circle_line_intersections x b c BC ABC); euclid_finish
  have hbet_exf : between e x f := by euclid_finish
  -- ray ex = ray ef (x between e,f); x splits ∠bec since x is between b and c
  euclid_apply (line_from_points e b) as EB
  euclid_apply (line_from_points e c) as EC
  have hx_off_EB : ¬ x.onLine EB := by euclid_finish
  have hx_off_EC : ¬ x.onLine EC := by euclid_finish
  euclid_apply (pasch_2 c x b EC)
  euclid_apply (pasch_2 b x c EB)
  euclid_apply (sum_angles_onlyif e b c x EB EC)
  euclid_finish

end Elements.Book3
