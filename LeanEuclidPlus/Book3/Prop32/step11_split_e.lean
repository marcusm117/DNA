import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Obtuse case: the antipode `a'` is in segment DCB (a'.opposingSides e BD). The chord `bd` splits the
-- right angle ∠a':b:e, giving ∠e:b:d = ∠a':b:e - ∠a':b:d = ∠b:a':d. (Mirror of step11_split, E side.)
theorem helper_3_32_step11_split_e (a' b d e f : Point) (ABCD : Circle) (BD BA EF : Line)
    (h_a'_circ : a'.onCircle ABCD) (h_b_circ : b.onCircle ABCD) (h_d_circ : d.onCircle ABCD)
    (h_a'_offBD : ¬a'.onLine BD) (h_e_offBD : ¬e.onLine BD) (h_a'e_opp : ¬a'.sameSide e BD)
    (h_b_BD : b.onLine BD) (h_d_BD : d.onLine BD) (h_bd : b ≠ d)
    (h_a'_BA : a'.onLine BA) (h_b_BA : b.onLine BA)
    (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_b_EF : b.onLine EF) (h_ebf : between e b f)
    (h_perp : ∠ a':b:f = ∟)
    (h_notint : ¬EF.intersectsCircle ABCD)
    (step7 : ∠ b:a':d + ∠ a':b:d = ∟) :
    ∠ e:b:d = ∠ b:a':d := by
  have h_perp_e : ∠ a':b:e = ∟ := by euclid_finish
  have h_a'_offEF : ¬a'.onLine EF := by euclid_finish
  have h_d_offEF : ¬d.onLine EF := by euclid_finish
  have h_a'd_EF : a'.sameSide d EF := by
    by_contra hcon
    euclid_apply (intersection_circle_line_1 a' d ABCD EF)
    euclid_finish
  euclid_apply (triple_incidence_2 EF BD BA b e d a')
  euclid_apply (sum_angles_onlyif b a' e d BA EF)
  euclid_finish

end Elements.Book3
