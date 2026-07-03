import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step13 (b c f g : Point)
    (h_step11 : |(b─f)| = |(c─g)|)
    (h_step12 : |(f─c)| = |(g─b)|) :
    (|(b─f)| = |(c─g)|) ∧ (|(f─c)| = |(g─b)|) :=
  ⟨h_step11, h_step12⟩

end Elements.Book1
