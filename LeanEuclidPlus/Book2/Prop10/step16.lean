import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
-- TODO (resume here): ∠DBG = ∟/2 via vertical angles (proposition_15 e g c d b EB AD → ∠e:b:c=∠d:b:g),
-- then linarith with ∠e:b:c=∟/2 (step14.2, via use_override step14.2 in Main).
-- BLOCKER: proposition_15 needs `between e b g`, whose SMT discharge over the full context times out.
-- DECOMPOSE: add a sub-node `step16_beg : between e b g` (b is EB∩AD, e above AD & g below AD on FD —
-- e.opposingSides g AD then the crossing gives betweenness). KEEP ∟/2 OUT OF SMT: prove the vertical
-- equality with `clear hassump` then combine via `linarith [hassump, hvert]` (∟/2 in hypothesis position
-- crashes the SMT translator — "Improper numeric").
theorem helper_2_10_step16 : ∠ d:b:g = ∟ / 2 := by sorry

end Elements.Book2
