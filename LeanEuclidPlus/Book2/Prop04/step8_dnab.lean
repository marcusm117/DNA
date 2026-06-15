import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.8 sub-sub: d ∉ AB. If d ∈ AB then a, b, d are collinear on AB (a, b already on AB) and the
   right angle ∠ b:a:d = ∟ becomes a degenerate/straight angle of three collinear points —
   impossible. -/
theorem helper_2_4_step8_dnab (a b d : Point) (AB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hab : a ≠ b) (had : a ≠ d)
    (hbad : ∠ b:a:d = ∟) :
    ¬(d.onLine AB) := by
  intro hdAB
  euclid_finish

end Elements.Book2
