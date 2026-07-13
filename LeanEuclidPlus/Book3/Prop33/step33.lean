import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- AF, FG equal to BF, FG: |af| = |bf| (from |af| = |fb|) and |fg| = |fg|.
theorem helper_3_33_step33
    (a b f g : Point)
    (hassump1 : |(a─f)| = |(f─b)|)   -- "$AF$ is equal to $FB$"
    (hassump2 : |(f─g)| = |(f─g)|)   -- "$FG$ (is) common"
    : |(a─f)| = |(b─f)| ∧ |(f─g)| = |(f─g)| := by
  euclid_finish

end Elements.Book3
