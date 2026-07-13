import SystemE
import Book3.Prop22.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_32_step12 (a b c d e f : Point) (ABCD : Circle) (BD EF : Line)
  (hassump1 : a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD)   -- "$ABCD$ is a quadrilateral in a circle"
  (h_b_BD : b.onLine BD) (h_d_BD : d.onLine BD) (h_bd : b ≠ d)
  (h_a_offBD : ¬a.onLine BD) (h_c_offBD : ¬c.onLine BD)
  (h_e_offBD : ¬e.onLine BD) (h_f_offBD : ¬f.onLine BD)
  (h_a_oppf : ¬a.sameSide f BD) (h_c_oppe : ¬c.sameSide e BD)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_b_EF : b.onLine EF) (h_ebf : between e b f) :
  ∠ b:a:d + ∠ b:c:d = ∟ + ∟ := by
  euclid_apply (line_from_points a c) as AC
  have hac : a.opposingSides c BD := by euclid_finish
  -- p = crossing point of chords AC and BD; show it is between b and d
  euclid_apply (intersection_lines_opposing a c BD AC)
  euclid_apply (intersection_lines BD AC) as p
  euclid_apply (pasch_4 a p c BD AC)
  euclid_apply (circle_points_between a c p ABCD)
  euclid_apply (circle_line_intersections p b d BD ABCD)
  have hdb : d.opposingSides b AC := by euclid_finish
  euclid_apply (Elements.Book3.proposition_22 a d c b ABCD AC BD)
  euclid_finish

end Elements.Book3
