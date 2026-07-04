import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
-- TODO: fill object/hypothesis binders (run --context step1)
theorem helper_1_27_step1
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : AE.intersectsLine FD)   -- "For if not"
  : g.sameSide b EF ∨ g.opposingSides b EF := by sorry

end Elements.Book1
