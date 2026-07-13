import SystemE
import Book3.Prop32.step_deg_ha
import Book3.Prop32.step_deg_hc
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Degenerate case of III.32: the chord $BD$ is a diameter, so $D$ coincides with the antipode $A'$.
-- Then both tangent angles ($\angle FBD$, $\angle EBD$) are right angles (perpendicular $BA'$), and
-- both segment angles ($\angle BAD = \angle BAA'$, $\angle DCB = \angle A'CB$) are right angles (angles
-- in a semi-circle). The two semi-circle right angles are the sub-nodes step_deg_ha / step_deg_hc.
theorem helper_3_32_step_deg (b a d c e f p a' o : Point) (ABCD : Circle) (EF BA BD : Line)
    (hdeg : d = a')
    (h_b_EF : b.onLine EF) (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ebf : between e b f)
    (h_notint : ¬EF.intersectsCircle ABCD)
    (h_b_circ : b.onCircle ABCD) (h_a_circ : a.onCircle ABCD) (h_c_circ : c.onCircle ABCD)
    (h_a'_circ : a'.onCircle ABCD)
    (h_b_BA : b.onLine BA) (h_p_BA : p.onLine BA) (h_a'_BA : a'.onLine BA) (h_ebp : ∠ e:b:p = ∟)
    (h_p_offEF : ¬p.onLine EF)
    (h_o_centre : o.isCentre ABCD) (h_a'ob : between a' o b)
    (h_a_offBD : ¬a.onLine BD) (h_c_offBD : ¬c.onLine BD) (h_b_BD : b.onLine BD) (h_d_BD : d.onLine BD) :
    ∠ f:b:d = ∠ b:a:d ∧ ∠ e:b:d = ∠ d:c:b := by
  -- tangent-side right angles: a' lies on BA ⟂ EF
  have h_fba' : ∠ f:b:a' = ∟ := by euclid_finish
  have h_eba' : ∠ e:b:a' = ∟ := by euclid_finish
  have h_boa' : between b o a' := by euclid_finish
  have h_a_offBA : ¬a.onLine BA := by euclid_finish
  have h_c_offBA : ¬c.onLine BA := by euclid_finish
  -- lines for the two semi-circle triangles (a and c each subtend the diameter b–a')
  euclid_apply (line_from_points a' a) as AaA
  euclid_apply (line_from_points b a) as BAl
  euclid_apply (line_from_points a' c) as AaC
  euclid_apply (line_from_points b c) as BCl
  have step_deg_ha : ∠ b:a:a' = ∟ := by euclid_apply (helper_3_32_step_deg_ha b a a' o ABCD BA AaA BAl (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onLine BA; assumption)) (by euclid_assumption "" (show a'.onLine BA; assumption)) (by euclid_assumption "" (show a.onLine AaA; assumption)) (by euclid_assumption "" (show a'.onLine AaA; assumption)) (by euclid_assumption "" (show a.onLine BAl; assumption)) (by euclid_assumption "" (show b.onLine BAl; assumption)) (by euclid_assumption "" (show ¬a.onLine BA; assumption)) (by euclid_assumption "" (show o.isCentre ABCD; assumption)) (by euclid_assumption "" (show between b o a'; assumption)))
  have step_deg_hc : ∠ b:c:a' = ∟ := by euclid_apply (helper_3_32_step_deg_hc b c a' o ABCD BA AaC BCl (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onLine BA; assumption)) (by euclid_assumption "" (show a'.onLine BA; assumption)) (by euclid_assumption "" (show c.onLine AaC; assumption)) (by euclid_assumption "" (show a'.onLine AaC; assumption)) (by euclid_assumption "" (show c.onLine BCl; assumption)) (by euclid_assumption "" (show b.onLine BCl; assumption)) (by euclid_assumption "" (show ¬c.onLine BA; assumption)) (by euclid_assumption "" (show o.isCentre ABCD; assumption)) (by euclid_assumption "" (show between b o a'; assumption)))
  euclid_apply (angle_symm b c a')
  euclid_finish

end Elements.Book3
