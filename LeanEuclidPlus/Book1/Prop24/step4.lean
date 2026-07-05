import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_24_step4
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─g)|)   -- "$AB$ is equal to $DE$ and $AC$ to $DG$"
  : |(b─a)| = |(e─d)| ∧ |(a─c)| = |(d─g)| := by
  exact ⟨by euclid_finish, hassump1.2⟩

end Elements.Book1
