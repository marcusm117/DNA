import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- AF, FG equal to BF, FG: |af| = |bf| (from |af| = |fb|) and |fg| = |fg|.
theorem helper_3_33_step7
    (a b f g : Point)
    (haffb : |(a─f)| = |(f─b)|) (hfgfg : |(f─g)| = |(f─g)|) :
    |(a─f)| = |(b─f)| ∧ |(f─g)| = |(f─g)| := by
  euclid_finish

end Elements.Book3
