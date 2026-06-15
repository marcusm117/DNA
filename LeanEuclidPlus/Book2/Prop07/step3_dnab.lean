import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: d ∉ AB. If d ∈ AB then a, b, d are collinear on AB, making the square's right angle
   ∠ b:a:d = ∟ a degenerate angle of three collinear points — impossible. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_dnab (a b d : Point) (AB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hab : a ≠ b) (had : a ≠ d)
    (hbad : ∠ b:a:d = ∟) :
    ¬(d.onLine AB) := by
  intro hon
  euclid_finish

end Elements.Book2
