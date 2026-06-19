import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- d∉BF. d∈AB, b∈AB∩BF, between c d b → d≠b.
   If d∈BF: d≠b; two_points → AB=BF; c∈AB=BF; c∈CE → CE∩BF, contradicts hCEBF. -/
theorem helper_2_5_step7_dfpar_doffBF (b c d : Point) (AB BF CE : Line)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB) (hbBF : b.onLine BF)
    (hcCE : c.onLine CE)
    (hCEBF : ¬(CE.intersectsLine BF))
    (hcdb : between c d b) :
    ¬(d.onLine BF) := by
  intro hdBF
  have hdb : d ≠ b := by euclid_finish
  have hcAB : c.onLine AB := by euclid_finish
  have hABBF : AB = BF := by
    euclid_apply (two_points_determine_line d b AB BF)
    euclid_finish
  have hcBF : c.onLine BF := hABBF ▸ hcAB
  have hCEneBF : CE ≠ BF := fun heq => hCEBF (by
    rw [heq]
    exact hCEBF)
  have hint : CE.intersectsLine BF := by
    euclid_apply (intersection_lines_common_point c CE BF)
    euclid_finish
  exact hCEBF hint

end Elements.Book2
