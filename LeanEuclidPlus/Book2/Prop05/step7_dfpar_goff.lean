import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- g∉BF. g∈EF, f∈EF∩BF, b∈BF, b∉EF.
   If g∈BF and EF=BF: b∈EF, contradiction.
   If g∈BF and EF≠BF: g∈EF∩BF, f∈EF∩BF, two_points → EF=BF, contradiction. -/
theorem helper_2_5_step7_dfpar_goff (b c d f g : Point) (AB BF DG EF : Line)
    (hgEF : g.onLine EF) (hfEF : f.onLine EF)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hgDG : g.onLine DG) (hdDG : d.onLine DG)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hcdb : between c d b)
    (hboffEF : ¬(b.onLine EF))
    (hEFAB : ¬(EF.intersectsLine AB))
    (hDGBF : ¬(DG.intersectsLine BF)) :
    ¬(g.onLine BF) := by
  intro hgBF
  have hEFneBF : EF ≠ BF := fun heq => hboffEF (heq ▸ hbBF)
  by_cases hgf : g = f
  · -- g = f: f ∈ DG ∩ BF; derive DG ≠ BF from AB ≠ BF, then contradiction
    have hfDG : f.onLine DG := hgf ▸ hgDG
    have hDGneBF : DG ≠ BF := by
      intro heq
      have hdBF : d.onLine BF := heq ▸ hdDG
      have hdb : d ≠ b := Ne.symm (between_symm b d c (between_symm c d b hcdb).1).2.1
      have hABeqBF : AB = BF := by
        euclid_apply (two_points_determine_line d b AB BF)
        euclid_finish
      have hfAB : f.onLine AB := hABeqBF.symm ▸ hfBF
      have hEFneAB : EF ≠ AB := fun h => hboffEF (h ▸ hbAB)
      exact hEFAB (by euclid_apply (intersection_lines_common_point f EF AB); euclid_finish)
    exact hDGBF (by euclid_apply (intersection_lines_common_point f DG BF); euclid_finish)
  · -- g ≠ f: g,f ∈ EF ∩ BF → EF = BF, contradicts b ∉ EF
    have hEFBF : EF = BF := by
      euclid_apply (two_points_determine_line g f EF BF)
      euclid_finish
    exact hboffEF (hEFBF ▸ hbBF)

end Elements.Book2
