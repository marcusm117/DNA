import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.2 sub: e ∉ AB. If e ∈ AB then c, d, e are collinear on AB and the right angle ∠d:c:e = ∟
   becomes a degenerate angle of three collinear points — impossible. The vertex c is distinct
   from both d (between a b d puts d past b, c between a b) and e (|c─e| = |c─d| > 0). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step2_eoff (a b c d e : Point) (AB : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟) :
    ¬(e.onLine AB) := by
  intro heAB
  euclid_finish

end Elements.Book2
