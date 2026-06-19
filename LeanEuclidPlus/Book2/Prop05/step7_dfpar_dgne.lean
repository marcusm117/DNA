import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- DG ≠ BF. If DG=BF: d∈BF; d≠b (betweenness); two_points_determine_line → AB=BF;
   c∈AB=BF with c∈CE → CE∩BF, contradicts hCEBF. -/
theorem helper_2_5_step7_dfpar_dgne (b c d : Point) (AB BF CE DG : Line)
    (hdDG : d.onLine DG)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB) (hbBF : b.onLine BF)
    (hcCE : c.onLine CE)
    (hCEBF : ¬(CE.intersectsLine BF))
    (hcdb : between c d b) :
    DG ≠ BF := by
  intro heq
  have hdBF : d.onLine BF := heq ▸ hdDG
  have hdb : d ≠ b := by euclid_finish
  have hABBF : AB = BF := by
    euclid_apply (two_points_determine_line d b AB BF)
    euclid_finish
  have hcAB : c.onLine AB := by euclid_finish
  exact hCEBF (by
    have hcBF : c.onLine BF := hABBF ▸ hcAB
    euclid_apply (intersection_lines_common_point c CE BF)
    euclid_finish)

end Elements.Book2
