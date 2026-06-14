import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.2: BG made equal to A [Prop.~1.3]. The length equality |bg| = |a₁a₂| is produced by the
   proposition_3 construction in Main; this helper repackages it. -/
theorem helper_2_1_step2 (a₁ a₂ b g : Point) (hbg : |(b─g)| = |(a₁─a₂)|) :
    |(b─g)| = |(a₁─a₂)| := by
  exact hbg

end Elements.Book2
