import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- BH much greater than HD: from between b g h, |b-h| = |b-g| + |g-h|; with BG = GD (step6) and
-- between g h d, |b-h| = |g-d| + |g-h| > |g-d| = |b-g| > |h-d|.
theorem helper_3_13_step8 (b g h d : Point)
    (step5 : between b g h ∧ between g h d)
    (step6 : |(b─g)| = |(g─d)|) :
    |(b─h)| > |(h─d)| := by euclid_finish

end Elements.Book3
