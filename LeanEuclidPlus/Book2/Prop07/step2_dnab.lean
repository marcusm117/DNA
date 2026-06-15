import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.2 sub: d ∉ AB. If d ∈ AB then a, b, d are collinear on AB (a, b already on AB), and the
   right angle ∠ b:a:d = ∟ would be an angle of three collinear points — impossible. a ≠ d is
   derived in-body from |a─d| = |a─b| together with a ≠ b. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step2_dnab (a b d : Point) (AB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hab : a ≠ b) (hadlen : |(a─d)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) :
    ¬(d.onLine AB) := by
  intro hon
  euclid_finish

end Elements.Book2
