import SystemE
import Book1.Prop05.Main
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- [Prop.~3.31] (angle in a semi-circle) is SUPPRESSED in Main: III.31 is skipped (horn-angle
-- addendum not formalizable in System E). The semicircle right angle — III.31's clean core — is
-- re-derived here inline from the isosceles triangles OA'D, OBD (I.5) + the triangle-angle-sum (I.32).
-- Here `a'` is the antipode (perpendicular endpoint); `d` on the circle subtends the diameter a'–b.
theorem helper_3_32_step6 (a' b d : Point) (ABCD : Circle) (BA BD AD : Line)
    (h_a'_circ : a'.onCircle ABCD) (h_b_circ : b.onCircle ABCD) (h_d_circ : d.onCircle ABCD)
    (h_a'_BA : a'.onLine BA) (h_b_BA : b.onLine BA)
    (h_d_BD : d.onLine BD) (h_b_BD : b.onLine BD) (h_bd : b ≠ d) (h_da' : d ≠ a')
    (h_a'_AD : a'.onLine AD) (h_d_AD : d.onLine AD)
    (step5 : ∃ o : Point, o.isCentre ABCD ∧ between a' o b ∧ a'.onCircle ABCD ∧ b.onCircle ABCD) :
    ∠ a':d:b = ∟ := by
  obtain ⟨o, ho_c, ho_bet, -, -⟩ := step5
  have h_d_offBA : ¬d.onLine BA := by euclid_finish
  euclid_apply (line_from_points o d) as OD
  euclid_apply (extend_point BA o a') as d1
  euclid_apply (extend_point OD o d) as e1
  euclid_apply (extend_point BA o b) as g1
  euclid_apply (extend_point BA a' b) as k
  -- isosceles base angles: |oa'|=|od| and |ob|=|od| (all radii)
  euclid_apply (Elements.Book1.proposition_5 o a' d d1 e1 BA AD OD)
  euclid_apply (Elements.Book1.proposition_5 o b d g1 e1 BA BD OD)
  -- three angles of triangle A'DB sum to two right-angles
  euclid_apply (Elements.Book1.proposition_32 d a' b k AD BA BD)
  euclid_finish

end Elements.Book3
