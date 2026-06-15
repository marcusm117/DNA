import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: the left half ADNC as formParallelogram a d c n AD CN AB DE (a,d on AD; c,n on CN;
   a,c on AB; d,n on DE; a.sameSide c DE; AD ∥ CN; AB ∥ DE). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_parL (a d c n : Point) (AD CN AB DE : Line)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hcCN : c.onLine CN) (hnCN : n.onLine CN)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (hnDE : n.onLine DE)
    (hCNAD : ¬(CN.intersectsLine AD)) (hABDE : ¬(AB.intersectsLine DE))
    (hasc : a.sameSide c DE) (hdn : d ≠ n) :
    formParallelogram a d c n AD CN AB DE := by
  euclid_intros
  have hADCN : ¬(AD.intersectsLine CN) := by
    intro hh; euclid_apply (intersection_symm AD CN); euclid_finish
  euclid_finish

end Elements.Book2
