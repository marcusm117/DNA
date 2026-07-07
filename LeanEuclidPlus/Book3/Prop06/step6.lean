import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step6 (f c e b : Point)
  (hstep5 : |(f─c)| = |(f─e)|)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(f─c)| = |(f─b)|)   -- "$FC$ was shown (to be) equal to $FB$"
  : |(f─e)| = |(f─b)| := by
  euclid_finish

end Elements.Book3
