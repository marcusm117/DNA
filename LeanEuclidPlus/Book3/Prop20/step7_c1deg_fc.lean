import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step7_c1deg_fc
  (a b c e f : Point) (BC AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_c_circ : c.onCircle ABC) (h_f_circ : f.onCircle ABC)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_bne_c : b ≠ c)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_bne_a : b ≠ a) (h_cne_a : c ≠ a) (h_aSe : a.sameSide e BC) (h_bet : between f e a)
  (step5 : ∠ b:e:f = ∠ e:a:b + ∠ e:a:b) (step6 : ∠ f:e:c = ∠ e:a:c + ∠ e:a:c)
  (hfeqc : f = c)
  : ∠ b:e:c = ∠ b:a:c + ∠ b:a:c := by
  -- f = c (AC a diameter): rays AE and AC coincide (E between A,C) ⟹ ∠EAB = ∠BAC;
  -- and step5 gives ∠BEC = ∠BEF = 2∠EAB.
  have hcea : between c e a := hfeqc ▸ h_bet
  euclid_apply (line_from_points a b) as AB
  euclid_apply (equal_angles a e c b b AEF AB)
  euclid_finish

end Elements.Book3
