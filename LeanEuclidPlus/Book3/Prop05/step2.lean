import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_step2 (EC : Line) (e c : Point)
    (heEC : e.onLine EC) (hcEC : c.onLine EC)
    : e.onLine EC ∧ c.onLine EC := by
  exact ⟨heEC, hcEC⟩

end Elements.Book3
