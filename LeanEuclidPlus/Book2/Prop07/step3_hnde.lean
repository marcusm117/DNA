import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: h ∉ DE. h and d both lie on AD, with d ∈ AD ∩ DE. If h ∈ DE then h, d are two common
   points of AD and DE; with h ≠ d this forces AD = DE, putting a (∈ AD) on DE — but a ∉ DE. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_hnde (a d h : Point) (AD DE : Line)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (hdDE : d.onLine DE)
    (hhd : h ≠ d) (hanDE : ¬(a.onLine DE)) :
    ¬(h.onLine DE) := by
  intro hhDE
  euclid_apply (two_points_determine_line h d AD DE)
  euclid_finish

end Elements.Book2
