import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.11 sub: ∠ h:d:n = ∟. h is between a and d on AD (step8_ahd) so ray d→h coincides with ray
   d→a; n is between d and e on DE (step11_dne) so ray d→n coincides with ray d→e. Hence
   ∠ h:d:n = ∠ a:d:e = ∟ (the square's right angle at d). -/
theorem helper_2_7_step11_rangle (a d e h n : Point) (AD DE : Line)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hnDE : n.onLine DE)
    (hade : ∠ a:d:e = ∟)
    (hahd : between a h d) (hdne : between d n e) :
    ∠ h:d:n = ∟ := by
  euclid_intros
  euclid_apply (equal_angles d h a n n AD DE)
  euclid_apply (equal_angles d n e h h DE AD)
  euclid_finish

end Elements.Book2
