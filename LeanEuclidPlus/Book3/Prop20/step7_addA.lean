import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step7_addA
  (a b c e f : Point) (BC AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_c_circ : c.onCircle ABC) (h_f_circ : f.onCircle ABC)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_bne_c : b ≠ c)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_bne_a : b ≠ a) (h_cne_a : c ≠ a) (h_aSe : a.sameSide e BC) (h_bet : between f e a)
  (hopp : a.opposingSides f BC)
  : ∠ b:a:c = ∠ b:a:e + ∠ e:a:c := by
  -- diameter AEF crosses BC at interior x; ray AE = ray AX (between a e x), x between b,c
  euclid_apply (intersection_lines_opposing a f BC AEF)
  have hcross : AEF.intersectsLine BC := by euclid_finish
  euclid_apply (intersection_lines AEF BC) as x
  have hbet_axf : between a x f := by euclid_apply (pasch_4 a x f BC AEF); euclid_finish
  have hx_in : x.insideCircle ABC := by euclid_apply (circle_points_between a f x ABC); euclid_finish
  have hbet_bxc : between b x c := by euclid_apply (circle_line_intersections x b c BC ABC); euclid_finish
  have hbet_aex : between a e x := by euclid_finish
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points a c) as AC
  have hx_off_AB : ¬ x.onLine AB := by euclid_finish
  have hx_off_AC : ¬ x.onLine AC := by euclid_finish
  euclid_apply (pasch_2 c x b AC)
  euclid_apply (pasch_2 b x c AB)
  euclid_apply (sum_angles_onlyif a b c x AB AC)
  euclid_finish

end Elements.Book3
