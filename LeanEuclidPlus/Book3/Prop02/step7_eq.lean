import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step7_eq (a b d p : Point) (DA AB DB : Line)
    (htri : formTriangle d a b DA AB DB)
    (hbase : ∠ d:a:b = ∠ d:b:a)
    (hbet : between a p b) :
    ∠ d:a:p = ∠ d:b:p := by
  euclid_finish

end Elements.Book3
