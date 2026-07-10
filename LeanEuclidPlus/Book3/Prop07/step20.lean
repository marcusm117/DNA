import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step20
    (ABCD : Circle) (e f g h : Point)
    (h_ctr : e.isCentre ABCD)
    (hh_on : h.onCircle ABCD)
    (hbet_efd : between e f d)
    (hh_ang_pre : ∠ f:e:h = ∠ g:e:f)
    : ∠ g:e:f = ∠ h:e:f := by
  have h_ne_e : h ≠ e := by euclid_finish
  have hef : e ≠ f := by euclid_finish
  exact hh_ang_pre.symm.trans (angle_symm h e f ⟨h_ne_e, hef⟩).symm

end Elements.Book3
