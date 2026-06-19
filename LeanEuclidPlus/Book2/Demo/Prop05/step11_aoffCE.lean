import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: a ∉ CE. If a ∈ CE: a,c ∈ AB ∩ CE (a≠c from between a c d) → AB = CE →
   d ∈ AB = CE, contradicting step11_doffCE (¬d.onLine CE). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_aoffCE (a c d : Point) (AB CE : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE)
    (hacd : between a c d)
    (hdoffCE : ¬(d.onLine CE)) :
    ¬(a.onLine CE) := by
  intro haCE
  have hac : a ≠ c := by euclid_finish
  have hABisCE : AB = CE := by
    euclid_apply (two_points_determine_line a c AB CE)
    euclid_finish
  exact hdoffCE (hABisCE ▸ hdAB)

end Elements.Book2
