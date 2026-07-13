import SystemE
import Book1.Prop11.Main
import Book3.Prop01.Main
import Book3.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_34_hEF_exists (b : Point) (ABC : Circle)
    (hb : b.onCircle ABC) :
    ∃ EF : Line, b.onLine EF ∧ ¬ EF.intersectsCircle ABC ∧
      (∀ FA : Line, b.onLine FA → FA ≠ EF → FA.intersectsCircle ABC) := by
  -- center o of ABC
  euclid_apply (proposition_1 ABC) as o
  euclid_apply (center_inside_circle o ABC)
  have hbo : b ≠ o := by euclid_finish
  -- diameter line through b and o
  euclid_apply (line_from_points b o) as BO
  -- antipode b2: extend from interior o through b to the far circle point
  euclid_apply (intersection_circle_line_extending_points ABC BO o b) as b2
  -- extend BO past b to b3 so that b is strictly between b2 and b3
  euclid_apply (extend_point BO b2 b) as b3
  -- perpendicular to BO at b (b between b2 and b3)
  euclid_apply (proposition_11 b2 b3 b BO) as f
  euclid_apply (line_from_points b f) as EF
  -- III.16: the perpendicular to the diameter at its end is tangent,
  -- and every other line through b meets the circle
  have H := proposition_16 b b2 o f ABC EF (by euclid_finish)
  exact ⟨EF, by euclid_finish, H.1.2, H.2⟩

end Elements.Book3
