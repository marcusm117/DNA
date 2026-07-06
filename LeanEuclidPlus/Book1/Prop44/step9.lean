import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step9
    (b e f g h : Point) (HB EF : Line)
    (step7 : ∠ b:h:f + ∠ f:g:e < ∟ + ∟)
    (step8 : ∠ b:h:f + ∠ f:g:e < ∟ + ∟ → HB.intersectsLine EF)
    : HB.intersectsLine EF :=
  step8 step7

end Elements.Book1
