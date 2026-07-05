import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_39_step4 (a d e c : Point) (AE BC EC : Line)
    (haonAE : a.onLine AE) (hasidedBC : a.sameSide d BC)
    (heonAE : e.onLine AE) (hconBC : c.onLine BC)
    (hAEnotBC : ¬AE.intersectsLine BC)
    (heonEC : e.onLine EC) (hconEC : c.onLine EC) :
    distinctPointsOnLine e c EC := by
  refine ⟨heonEC, hconEC, ?_⟩
  intro hec
  subst hec
  have haoffBC : ¬(a.onLine BC) := same_side_not_on_line a d BC hasidedBC
  have hAEneBC : AE ≠ BC := fun h => haoffBC (h ▸ haonAE)
  exact hAEnotBC (by euclid_apply (intersection_lines_common_point e AE BC); euclid_finish)

end Elements.Book1
