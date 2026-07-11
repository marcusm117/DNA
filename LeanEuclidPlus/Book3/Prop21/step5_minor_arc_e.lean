import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_21_step5_minor_arc_e
    (e b d f' : Point) (BD : Line) (ABCD : Circle)
    (h_f'_centre : f'.isCentre ABCD)
    (h_e_circ : e.onCircle ABCD)
    (h_b_circ : b.onCircle ABCD)
    (h_d_circ : d.onCircle ABCD)
    (h_bd : distinctPointsOnLine b d BD)
    (h_e_off : ¬ e.onLine BD)
    (h_major : ¬ e.sameSide f' BD) :
    ∠ b:e:d + ∠ b:e:d + ∠ b:f':d = ∟ + ∟ + ∟ + ∟ := by
  obtain ⟨h_b_on, h_d_on, h_bd_ne⟩ := h_bd
  have h_ef' : e ≠ f' := by euclid_finish
  have h_f'_in : f'.insideCircle ABCD := by euclid_finish
  -- diameter EF through e and the centre; antipode X of e
  euclid_apply (line_from_points e f') as EF
  euclid_apply (intersection_circle_line_extending_points ABCD EF f' e) as X
  have h_bet_eX : between e f' X := by euclid_finish
  -- exterior-angle triangles at the centre (Prop 1.32)
  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points d e) as DE
  euclid_apply (line_from_points b f') as BFc
  euclid_apply (line_from_points d f') as DFc
  have htri_b : formTriangle b e f' BE EF BFc := by euclid_finish
  euclid_apply (Elements.Book1.proposition_32 b e f' X BE EF BFc)
  have htri_d : formTriangle d e f' DE EF DFc := by euclid_finish
  euclid_apply (Elements.Book1.proposition_32 d e f' X DE EF DFc)
  -- foot point on BD giving the ray decompositions
  by_cases h_diam : f'.onLine BD
  · have h_bfd : between b f' d := by euclid_finish
    euclid_finish
  · have h_opp : e.opposingSides f' BD := by euclid_finish
    euclid_apply (intersection_lines_opposing e f' BD EF)
    euclid_apply (intersection_lines BD EF) as g
    have h_egf : between e g f' := by euclid_finish
    have h_g_in : g.insideCircle ABCD := by euclid_finish
    have h_bgd : between b g d := by euclid_finish
    euclid_finish

end Elements.Book3
