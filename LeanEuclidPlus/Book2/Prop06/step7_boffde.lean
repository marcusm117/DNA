import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: b ∉ DE. If b ∈ DE then b, d (distinct on AB, b ≠ d from between a b d) both lie on DE,
   so DE = AB (two_points_determine_line), putting e ∈ AB — contradicting step2_eoff (degeneracy). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step7_boffde (a b c d e : Point) (AB DE : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟) :
    ¬(b.onLine DE) := by
  have step2_eoff : ¬(e.onLine AB) := by sorry
  intro hbDE
  euclid_apply (two_points_determine_line b d DE AB)
  euclid_finish

end Elements.Book2
