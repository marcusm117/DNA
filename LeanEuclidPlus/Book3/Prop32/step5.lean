import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_32_step5 (a' b : Point) (ABCD : Circle) (BA : Line)
    (h_a'_BA : a'.onLine BA) (h_b_BA : b.onLine BA) (h_ab : b ≠ a')
    (h_a'_circ : a'.onCircle ABCD) (h_b_circ : b.onCircle ABCD)
    (step4 : ∀ o : Point, o.isCentre ABCD → o.onLine BA) :
    ∃ o : Point, o.isCentre ABCD ∧ between a' o b ∧ a'.onCircle ABCD ∧ b.onCircle ABCD := by
  euclid_apply (exists_centre ABCD) as o
  euclid_apply (step4 o)
  euclid_finish

end Elements.Book3
