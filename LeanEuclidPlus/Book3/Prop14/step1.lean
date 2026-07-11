import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step1
    (e e' : Point) (ABDC : Circle)
    (he : e.isCentre ABDC) (he' : e'.isCentre ABDC) :
    e'.isCentre ABDC ∧ e' = e := by
  have heqe : e' = e := by euclid_finish
  exact ⟨he', heqe⟩

end Elements.Book3
