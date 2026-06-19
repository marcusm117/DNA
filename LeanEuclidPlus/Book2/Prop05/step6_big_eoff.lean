import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub-sub-sub: e ∉ AB. If e ∈ AB then b, c, e are collinear on AB and the right angle
   ∠b:c:e = ∟ at c becomes a degenerate angle of three collinear points — impossible. The vertex c
   is distinct from b (between c d b ⟹ c ≠ b) and from e (|c─e| = |c─b| > 0). Minimal signature. -/
theorem helper_2_5_step6_big_eoff (b c d e : Point) (AB : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hcdb : between c d b) (hce : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟) :
    ¬(e.onLine AB) := by
  intro heAB
  euclid_finish

end Elements.Book2
