import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: d ∉ BF. d ∈ DG; if d ∈ BF then DG and BF share point d, contradicting DG ∥ BF. -/
-- We need an off-DG or off-BF anchor to establish DG ≠ BF before calling common_point.
-- Use: b ∈ BF, b ∈ AB; d ∈ DG. Step6's boffdg (b ∉ DG) gives DG ≠ BF via b: if DG = BF then b ∈ DG.
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_doffbf (b d : Point) (DG BF : Line)
    (hdDG : d.onLine DG) (hbBF : b.onLine BF)
    (hboffDG : ¬(b.onLine DG))
    (hDGBF : ¬(DG.intersectsLine BF)) :
    ¬(d.onLine BF) := by
  intro hdBF
  have hDGneBF : DG ≠ BF := fun heq => hboffDG (heq ▸ hbBF)
  euclid_apply (intersection_lines_common_point d DG BF)
  euclid_finish

end Elements.Book2
