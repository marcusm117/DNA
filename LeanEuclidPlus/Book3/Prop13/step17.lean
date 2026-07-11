import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Take any point r between d and b. By step15 it is inside EBFD; by step16 it is outside EBFD — absurd.
theorem helper_3_13_step17 (ABDC EBFD : Circle) (d b : Point) (AC : Line)
    (step15 : ∀ r : Point, between d r b → r.insideCircle ABDC ∧ r.insideCircle EBFD)
    (step16 : ∀ r : Point, between d r b → r.insideCircle ABDC ∧ r.outsideCircle EBFD)
    (hdAC : d.onLine AC) (hbAC : b.onLine AC) (hdb : d ≠ b) :
    False := by
  obtain ⟨r, hr_AC, hr_bet⟩ := exists_point_between_points_on_line AC d b (by euclid_finish)
  have h1 := (step15 r hr_bet).2
  have h2 := (step16 r hr_bet).2
  euclid_finish

end Elements.Book3
