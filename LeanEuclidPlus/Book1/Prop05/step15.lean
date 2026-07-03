import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step15 (a b c : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (ha_ne_b : a ≠ b)
    (hACneAB : AC ≠ AB) :
    distinctPointsOnLine b c BC := by
  refine ⟨hbBC, hcBC, ?_⟩
  intro hbc
  have hbAC : b.onLine AC := hbc ▸ hcAC
  exact hACneAB (two_points_determine_line a b AB AC ⟨⟨haAB, hbAB, ha_ne_b⟩, haAC, hbAC⟩).symm

end Elements.Book1
