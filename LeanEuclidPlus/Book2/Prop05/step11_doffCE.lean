import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: d ∉ CE. d ∈ DG; DG ≠ CE (step11_DGneCE); if d ∈ CE then
   intersection_lines_common_point d DG CE gives DG.intersectsLine CE — contradicts hDGCE. -/
theorem helper_2_5_step11_doffCE (d : Point) (DG CE : Line)
    (hdDG : d.onLine DG)
    (hDGneCE : DG ≠ CE)
    (hDGCE : ¬(DG.intersectsLine CE)) :
    ¬(d.onLine CE) := by
  intro hdCE
  euclid_apply (intersection_lines_common_point d DG CE)
  euclid_finish

end Elements.Book2
