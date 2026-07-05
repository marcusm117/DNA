import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step6_ss (a e b : Point) (CH : Line)
  (h_step6_ss_ssa : e.sameSide a CH)
  (h_step6_ss_ssb : a.sameSide b CH) :
  e.sameSide b CH := by
  euclid_apply (same_side_symm e a CH)
  euclid_apply (same_side_trans a e b CH)
  assumption

end Elements.Book1
