import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: f ∉ AB. If f ∈ AB then c, d, f are collinear on AB (c, d already on AB) and the right
   angle ∠c:d:f = ∟ at d becomes a degenerate angle of three collinear points — impossible. d is
   distinct from c (between a c b: c between a,b; between a b d: d beyond b) and from f (|d─f| =
   |c─d| > 0, since c ≠ d). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step7_foffab (a b c d f : Point) (AB : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hdf : |(d─f)| = |(c─d)|) (hcdf : ∠ c:d:f = ∟) :
    ¬(f.onLine AB) := by
  intro hfAB
  euclid_finish

end Elements.Book2
