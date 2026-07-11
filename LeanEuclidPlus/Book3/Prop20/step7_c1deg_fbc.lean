import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step7_c1deg_fbc
  (b c e f : Point) (BC : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_b_circ : b.onCircle ABC) (h_c_circ : c.onCircle ABC)
  (h_f_circ : f.onCircle ABC)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (hfBC : f.onLine BC) (h_bne_c : b ≠ c)
  : f = b ∨ f = c := by
  rcases Classical.em (f = b) with h | hfb
  · exact Or.inl h
  · rcases Classical.em (f = c) with h | hfc
    · exact Or.inr h
    · exfalso
      rcases between_points f b c BC ⟨hfb, h_bne_c, Ne.symm hfc, hfBC, h_b_BC, h_c_BC⟩ with h | h | h
      · euclid_finish
      · euclid_finish
      · euclid_finish

end Elements.Book3
