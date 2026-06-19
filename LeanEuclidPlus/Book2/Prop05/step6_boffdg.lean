import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: b ∉ DG. b, d are distinct on AB (b ≠ d from between c d b). d ∈ DG. If b ∈ DG then b, d
   are two distinct points on both AB and DG, forcing AB = DG (two_points_determine_line), putting the
   off-AB point e onto AB-via-DG... simplest: AB = DG ⟹ c ∈ DG, but DG ∥ CE and c ∈ CE ⟹ c on both,
   DG = CE, contradiction. Uses d ∉ CE (step6_doffce) to pin DG ≠ CE indirectly; here euclid_finish
   closes from AB = DG + the parallel DG ∥ CE + c ∈ AB ∩ CE. -/
theorem helper_2_5_step6_boffdg (b c d : Point) (AB CE DG : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (hdDG : d.onLine DG)
    (hcdb : between c d b) (hDGCE : ¬(DG.intersectsLine CE)) (hdoffCE : ¬(d.onLine CE)) :
    ¬(b.onLine DG) := by
  intro hbDG
  have hbd : b ≠ d := by euclid_finish
  euclid_apply (two_points_determine_line b d AB DG)
  euclid_finish

end Elements.Book2
