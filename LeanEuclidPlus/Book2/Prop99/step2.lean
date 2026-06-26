import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_99_step2 (a c e : Point)
  -- Reasoning hypotheses (from @assumption — do NOT remove these types from the signature):
  (hassump1 : |(a─c)| = |(a─c)|)   -- "AC equals AC"
  : |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)| := rfl

end Elements.Book2
