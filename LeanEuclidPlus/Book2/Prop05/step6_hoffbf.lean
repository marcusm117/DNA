import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: h ∉ BF. h ∈ DG; b ∉ DG (step6_boffdg) gives DG ≠ BF; then if h ∈ BF,
   intersection_lines_common_point h DG BF contradicts DG ∥ BF. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_hoffbf (b h : Point) (DG BF : Line)
    (hhDG : h.onLine DG) (hbBF : b.onLine BF)
    (hboffDG : ¬(b.onLine DG))
    (hDGBF : ¬(DG.intersectsLine BF)) :
    ¬(h.onLine BF) := by
  intro hhBF
  have hDGneBF : DG ≠ BF := fun heq => hboffDG (heq ▸ hbBF)
  euclid_apply (intersection_lines_common_point h DG BF)
  euclid_finish

end Elements.Book2
