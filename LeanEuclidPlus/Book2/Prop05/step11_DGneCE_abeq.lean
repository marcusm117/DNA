import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub-sub: AB = CE. c,d ∈ AB ∩ CE with c ≠ d → two_points_determine_line. -/
-- After hDGeqCE : DG = CE substitution, CE is already AB in context.
-- So hcCE : c.onLine CE = c.onLine AB (after subst), and goal AB = CE becomes AB = AB.
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_DGneCE_abeq (c d : Point) (AB CE : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (hdCE : d.onLine CE)
    (hcd : c ≠ d) :
    AB = CE := by
  euclid_finish

end Elements.Book2
