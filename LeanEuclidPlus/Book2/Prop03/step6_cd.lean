import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact: c ≠ d. |c─d| = |c─b| and c ≠ b (between a c b), so |c─b| > 0 = |c─d| would fail if
   c = d; hence c ≠ d. -/
theorem helper_2_3_step6_cd (a b c d : Point)
    (hacb : between a c b) (hcdlen : |(c─d)| = |(c─b)|) : c ≠ d := by
  euclid_finish

end Elements.Book2
