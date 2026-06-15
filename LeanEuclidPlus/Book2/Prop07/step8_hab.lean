import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.8 sub: ∠ h:a:b = ∟. h is between a and d on AD (step8_ahd), so the ray a→h coincides with the
   ray a→d; hence ∠ h:a:b = ∠ d:a:b = ∟ (the square's right angle at a). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step8_hab (a b d h : Point) (AB AD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAD : a.onLine AD) (hhAD : h.onLine AD) (hdAD : d.onLine AD)
    (hab : a ≠ b) (hbad : ∠ b:a:d = ∟)
    (hahd : between a h d) :
    ∠ h:a:b = ∟ := by
  euclid_intros
  euclid_apply (equal_angles a h d b b AD AB)
  euclid_finish

end Elements.Book2
