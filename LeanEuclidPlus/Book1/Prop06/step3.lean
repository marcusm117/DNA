import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/- 1.6.3: DB, equal to the lesser AC, cut off from the greater AB [Prop.~1.3]. The `proposition_3
   b a a c AB AC` construction in Main produces `d` together with `between b d a` and
   `|(b─d)| = |(a─c)|`; this helper repackages those two postcondition facts. -/
theorem helper_1_6_step3 (a b c d : Point) (hbtw : between b d a) (heq : |(b─d)| = |(a─c)|) :
    between b d a ∧ |(b─d)| = |(a─c)| := by
  exact ⟨hbtw, heq⟩

end Elements.Book1
