import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- AB cut in half at F (Prop 1.10, construction arm): between a f b and |af| = |fb|.
theorem helper_3_33_step4
    (a b f : Point)
    (hafb : between a f b) (haffb : |(a─f)| = |(f─b)|) :
    between a f b ∧ |(a─f)| = |(f─b)| :=
  ⟨hafb, haffb⟩

end Elements.Book3
