import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step8_dnp_qpmn (g k n q r p : Point) (MN OP CH BL DF : Line)
    (h_gkqr : formParallelogram g k q r MN OP CH BL)
    (h_knrp : formParallelogram k n r p MN OP BL DF) :
    q.sameSide p MN := by
  euclid_apply (parallelogram_same_side g k q r MN OP CH BL)
  euclid_apply (parallelogram_same_side k n r p MN OP BL DF)
  euclid_apply (same_side_symm q r MN)
  euclid_apply (same_side_trans r q p MN)
  euclid_finish

end Elements.Book2
