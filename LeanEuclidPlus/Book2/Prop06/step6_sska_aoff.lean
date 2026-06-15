import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6 / step6_sska: a ∉ CE. Reuse step2_eoff for the hard part (e ∉ AB, the angle
   degeneracy from ∠d:c:e = ∟). Then if a ∈ CE, a and c (distinct on AB, a≠c from between a c b) both
   lie on CE, so CE = AB (two_points_determine_line); then e ∈ CE = AB contradicts e ∉ AB. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step6_sska_aoff (a b c d e : Point) (AB CE : Line)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟) :
    ¬(a.onLine CE) := by
  euclid_intros
  have step2_eoff : ¬(e.onLine AB) := by sorry
  euclid_apply (two_points_determine_line a c CE AB)
  euclid_finish

end Elements.Book2
