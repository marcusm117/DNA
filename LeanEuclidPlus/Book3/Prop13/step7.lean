import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- BG > HD: from between g h d, |g-d| = |g-h| + |h-d| > |h-d|, and BG = GD (step6).
theorem helper_3_13_step7 (b g h d : Point)
    (step5 : between b g h ∧ between g h d)
    (step6 : |(b─g)| = |(g─d)|) :
    |(b─g)| > |(h─d)| := by euclid_finish

end Elements.Book3
