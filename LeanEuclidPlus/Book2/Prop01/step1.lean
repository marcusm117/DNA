import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.1: BF drawn from B at right-angles to BC [Prop.~1.11]. The right angle ∠f:b:c = ∟ is
   produced by the proposition_11'' construction in Main; this helper repackages it. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step1 (b c f : Point) (hfbc : ∠ f:b:c = ∟) :
    ∠ f:b:c = ∟ := by
  exact hfbc

end Elements.Book2
