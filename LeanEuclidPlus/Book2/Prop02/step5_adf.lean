import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.5: ∠a:d:f = ∟. f lies on DE on the same ray from d as e (between d f e), so
   the angle ∠a:d:f equals ∠a:d:e = ∟. -/
theorem helper_2_2_step5_adf (a d e f : Point) (AD DE : Line)
    (hade : ∠ a:d:e = ∟) (hdfe : between d f e) (hadne : a ≠ d)
    (hdAD : d.onLine AD) (haAD : a.onLine AD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE) :
    ∠ a:d:f = ∟ := by
  euclid_intros
  euclid_apply (equal_angles d e f a a DE AD)
  euclid_finish

end Elements.Book2
