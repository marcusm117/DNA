import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- The perpendicular endpoint `a'` lies on `BA` (⟂ `EF` at `b`, via the perpendicular point `p`), and
-- `a' ≠ b` (it is the far intersection of the diameter). [Prop.~1.11] is satisfied by the construction
-- arm (proposition_11 is applied `as p` in Main).
theorem helper_3_32_step1 (b a' p e f o : Point) (ABCD : Circle) (EF BA : Line)
    (h_b_EF : b.onLine EF) (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ebf : between e b f)
    (h_b_BA : b.onLine BA) (h_p_BA : p.onLine BA) (h_a'_BA : a'.onLine BA)
    (h_ebp : ∠ e:b:p = ∟) (h_p_offEF : ¬p.onLine EF)
    (h_o_centre : o.isCentre ABCD) (h_a'ob : between a' o b) :
    distinctPointsOnLine b a' BA ∧ ∠ a':b:f = ∟ := by
  euclid_finish

end Elements.Book3
