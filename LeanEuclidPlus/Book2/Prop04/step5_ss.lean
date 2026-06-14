import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.5 sub: c and a are on the same side of the diagonal BD. c is between a and b on AB, and the
   endpoint b lies on BD while a does not; so along the segment b→c→a, c and a fall on the same
   side of BD (pasch_2). Requires c ∉ BD, which holds because c ∈ AB, c ≠ b, and AB meets BD only
   at b. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step5_ss (a b c d : Point) (AB BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d) (had : a ≠ d)
    (hbad : ∠ b:a:d = ∟) :
    c.sameSide a BD := by
  euclid_intros
  euclid_apply (pasch_2 b c a BD)
  euclid_finish

end Elements.Book2
