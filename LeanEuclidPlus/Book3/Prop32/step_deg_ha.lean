import SystemE
import Book1.Prop05.Main
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Angle in a semi-circle (III.31's core, re-derived from I.5 + I.32 since III.31 is skipped):
-- `a` on the circle subtends the diameter `b`–`a'` (centre `o` between them), so ∠b:a:a' = ∟.
theorem helper_3_32_step_deg_ha (b a a' o : Point) (ABCD : Circle) (BA AaA BAl : Line)
    (h_b_circ : b.onCircle ABCD) (h_a_circ : a.onCircle ABCD) (h_a'_circ : a'.onCircle ABCD)
    (h_b_BA : b.onLine BA) (h_a'_BA : a'.onLine BA)
    (h_a_AaA : a.onLine AaA) (h_a'_AaA : a'.onLine AaA)
    (h_a_BAl : a.onLine BAl) (h_b_BAl : b.onLine BAl)
    (h_a_offBA : ¬a.onLine BA)
    (h_o_centre : o.isCentre ABCD) (h_boa' : between b o a') :
    ∠ b:a:a' = ∟ := by
  euclid_apply (line_from_points o a) as OA
  euclid_apply (extend_point BA o b) as d1
  euclid_apply (extend_point OA o a) as e1
  euclid_apply (extend_point BA o a') as g1
  euclid_apply (extend_point BA b a') as k
  -- isosceles base angles: |ob| = |oa| and |oa'| = |oa| (all radii)
  euclid_apply (Elements.Book1.proposition_5 o b a d1 e1 BA BAl OA)
  euclid_apply (Elements.Book1.proposition_5 o a' a g1 e1 BA AaA OA)
  -- three angles of triangle a-b-a' sum to two right-angles
  euclid_apply (Elements.Book1.proposition_32 a b a' k BAl BA AaA)
  euclid_finish

end Elements.Book3
