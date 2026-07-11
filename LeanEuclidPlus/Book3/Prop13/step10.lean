import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- BH is both = HD (step9) and > HD (shown much greater) — impossible.
theorem helper_3_13_step10 (b h d : Point)
    (step10_assumption1 : |(b─h)| > |(h─d)|)
    (step9 : |(b─h)| = |(h─d)|) :
    False := by euclid_finish

end Elements.Book3
