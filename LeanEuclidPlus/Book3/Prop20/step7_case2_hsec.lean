import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step7_case2_hsec
  (a b c e f : Point) (BC AEF AB AC EB EC : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_c_circ : c.onCircle ABC) (h_f_circ : f.onCircle ABC)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_bne_c : b ≠ c)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC)
  (h_e_EB : e.onLine EB) (h_b_EB : b.onLine EB) (h_e_EC : e.onLine EC) (h_c_EC : c.onLine EC)
  (h_bne_a : b ≠ a) (h_cne_a : c ≠ a) (h_aSe : a.sameSide e BC) (h_bet : between f e a)
  (hfs : f.sameSide a BC)
  : (f.sameSide b EC ∧ e.sameSide b AC ∧ c.sameSide b AEF) ∨
    (f.sameSide c EB ∧ e.sameSide c AB ∧ b.sameSide c AEF) := by
  -- b,c on the same side of diameter AEF (case 2): crossing x = AEF∩BC is outside the circle.
  have hcbAEF : c.sameSide b AEF := by
    by_cases hpar : AEF.intersectsLine BC
    · euclid_apply (intersection_lines AEF BC) as x
      have h1 : ¬ between a x f := by euclid_finish
      have h2 : x.outsideCircle ABC := by euclid_finish
      euclid_finish
    · euclid_finish
  by_cases hE : f.sameSide b EC
  · left
    exact ⟨hE, by euclid_finish, hcbAEF⟩
  · right
    exact ⟨by euclid_finish, by euclid_finish, by euclid_finish⟩

end Elements.Book3
