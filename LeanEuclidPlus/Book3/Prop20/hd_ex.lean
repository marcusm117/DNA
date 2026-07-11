import SystemE
import Book1.Prop31.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_hd_ex
  (a b c e : Point) (BC : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_bne_c : b ≠ c)
  (h_aSe : a.sameSide e BC)
  : ∃ d : Point, d.onCircle ABC ∧ b ≠ d ∧ c ≠ d ∧ a ≠ d ∧ d.sameSide e BC := by
  -- A line Q through the centre e parallel to BC is a diameter; BOTH its circle-intersections
  -- lie on e's side of BC, so at least one differs from a. (d.sameSide e BC ⟹ d ≠ b,c for free.)
  have he_off_BC : ¬ e.onLine BC := by euclid_finish
  euclid_apply (Elements.Book1.proposition_31 e b c BC) as Q
  euclid_apply (intersection_circle_line_2 e ABC Q)
  euclid_apply (intersections_circle_line ABC Q) as (q1, q2)
  by_cases hq1a : q1 = a
  · exact ⟨q2, by euclid_finish, by euclid_finish, by euclid_finish, by euclid_finish, by euclid_finish⟩
  · exact ⟨q1, by euclid_finish, by euclid_finish, by euclid_finish, by euclid_finish, by euclid_finish⟩

end Elements.Book3
