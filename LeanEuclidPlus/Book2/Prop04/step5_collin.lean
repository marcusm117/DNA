import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.5 sub-sub: a, b, d collinear on AD ⟹ ∠ b:a:d ≠ ∟. a ≠ b (a-c-b are between) and a ≠ d
   (else the angle is undefined / they coincide); three distinct collinear points make ∠ b:a:d
   degenerate (0 or ∟+∟), never the right angle. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step5_collin (a b c d : Point) (AD : Line)
    (hacb : between a c b)
    (haAD : a.onLine AD) (hbAD : b.onLine AD) (hdAD : d.onLine AD)
    (hab : a ≠ b) (had : a ≠ d) :
    ∠ b:a:d ≠ ∟ := by
  euclid_finish

end Elements.Book2
