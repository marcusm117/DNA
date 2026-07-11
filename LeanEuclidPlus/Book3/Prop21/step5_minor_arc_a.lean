import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_21_step5_minor_arc_a
    (a b d f' : Point) (BD : Line) (ABCD : Circle)
    (h_f'_centre : f'.isCentre ABCD)
    (h_a_circ : a.onCircle ABCD)
    (h_b_circ : b.onCircle ABCD)
    (h_d_circ : d.onCircle ABCD)
    (h_bd : distinctPointsOnLine b d BD)
    (h_a_off : ¬ a.onLine BD)
    (h_major : ¬ a.sameSide f' BD) :
    ∠ b:a:d + ∠ b:a:d + ∠ b:f':d = ∟ + ∟ + ∟ + ∟ := by
  obtain ⟨h_b_on, h_d_on, h_bd_ne⟩ := h_bd
  have h_af' : a ≠ f' := by euclid_finish
  have h_f'_in : f'.insideCircle ABCD := by euclid_finish
  -- diameter AF through a and the centre; antipode X of a
  euclid_apply (line_from_points a f') as AF
  euclid_apply (intersection_circle_line_extending_points ABCD AF f' a) as X
  have h_bet_aX : between a f' X := by euclid_finish
  -- exterior-angle triangles at the centre (Prop 1.32)
  euclid_apply (line_from_points b a) as BA
  euclid_apply (line_from_points d a) as DA
  euclid_apply (line_from_points b f') as BFc
  euclid_apply (line_from_points d f') as DFc
  have htri_b : formTriangle b a f' BA AF BFc := by euclid_finish
  euclid_apply (Elements.Book1.proposition_32 b a f' X BA AF BFc)
  have htri_d : formTriangle d a f' DA AF DFc := by euclid_finish
  euclid_apply (Elements.Book1.proposition_32 d a f' X DA AF DFc)
  -- foot point on BD giving the ray decompositions
  by_cases h_diam : f'.onLine BD
  · have h_bfd : between b f' d := by euclid_finish
    euclid_finish
  · have h_opp : a.opposingSides f' BD := by euclid_finish
    euclid_apply (intersection_lines_opposing a f' BD AF)
    euclid_apply (intersection_lines BD AF) as g
    have h_agf : between a g f' := by euclid_finish
    have h_g_in : g.insideCircle ABCD := by euclid_finish
    have h_bgd : between b g d := by euclid_finish
    euclid_finish

end Elements.Book3
