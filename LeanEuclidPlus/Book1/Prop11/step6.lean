import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
-- TODO: fill object/hypothesis binders (run --context step6)
theorem helper_1_11_step6
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(c─d)| = |(c─e)|)   -- "$DC$ is equal to $CE$"
  (hassump2 : |(c─f)| = |(c─f)|)   -- "$CF$ is common"
  : |(c─d)| = |(c─e)| ∧ |(c─f)| = |(c─f)| := by
  exact ⟨hassump1, hassump2⟩

end Elements.Book1
