import SystemE
import Book1.Prop05.Main
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Angle in a semi-circle (III.31's core, re-derived from I.5 + I.32 since III.31 is skipped):
-- `c` on the circle subtends the diameter `b`–`a'` (centre `o` between them), so ∠b:c:a' = ∟.
theorem helper_3_32_step_deg_hc (b c a' o : Point) (ABCD : Circle) (BA AaC BCl : Line)
    (h_b_circ : b.onCircle ABCD) (h_c_circ : c.onCircle ABCD) (h_a'_circ : a'.onCircle ABCD)
    (h_b_BA : b.onLine BA) (h_a'_BA : a'.onLine BA)
    (h_c_AaC : c.onLine AaC) (h_a'_AaC : a'.onLine AaC)
    (h_c_BCl : c.onLine BCl) (h_b_BCl : b.onLine BCl)
    (h_c_offBA : ¬c.onLine BA)
    (h_o_centre : o.isCentre ABCD) (h_boa' : between b o a') :
    ∠ b:c:a' = ∟ := by
  euclid_apply (line_from_points o c) as OC
  euclid_apply (extend_point BA o b) as d1
  euclid_apply (extend_point OC o c) as e1
  euclid_apply (extend_point BA o a') as g1
  euclid_apply (extend_point BA b a') as k
  euclid_apply (Elements.Book1.proposition_5 o b c d1 e1 BA BCl OC)
  euclid_apply (Elements.Book1.proposition_5 o a' c g1 e1 BA AaC OC)
  euclid_apply (Elements.Book1.proposition_32 c b a' k BCl BA AaC)
  euclid_finish

end Elements.Book3
