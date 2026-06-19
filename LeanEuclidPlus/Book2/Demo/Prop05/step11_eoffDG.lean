import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: e ∉ DG. e ∈ CE; DG ≠ CE (step11_DGneCE); if e ∈ DG then
   intersection_lines_common_point e DG CE gives DG.intersectsLine CE — contradicts hDGCE. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_eoffDG (e : Point) (DG CE : Line)
    (heCE : e.onLine CE)
    (hDGneCE : DG ≠ CE)
    (hDGCE : ¬(DG.intersectsLine CE)) :
    ¬(e.onLine DG) := by
  intro heDG
  euclid_apply (intersection_lines_common_point e DG CE)
  euclid_finish

end Elements.Book2
