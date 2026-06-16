import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: a ∉ CE. If a ∈ CE and c ∈ CE and between a c d:
   euclid_finish can derive d ∈ CE (collinearity + CE containment), then d ∈ DG and DG ∥ CE →
   contradiction via intersection_lines_common_point d DG CE. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_klh_aaoff (a c d e : Point) (AB CE DG : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hdDG : d.onLine DG)
    (hacd : between a c d) (heoffDG : ¬(e.onLine DG))
    (hDGCE : ¬(DG.intersectsLine CE)) :
    ¬(a.onLine CE) := by
  intro haCE
  have hac : a ≠ c := (between_symm a c d hacd).1
  have hDGneCE : DG ≠ CE := fun heq => heoffDG (heq ▸ heCE)
  have hABisCE : AB = CE := by
    euclid_apply (two_points_determine_line a c AB CE)
    euclid_finish
  have hdCE : d.onLine CE := hABisCE ▸ hdAB
  euclid_apply (intersection_lines_common_point d DG CE)
  euclid_finish

end Elements.Book2
