import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- d∉EF. d∈DG, g∈DG∩EF, between c d b → c,d,b on AB (c∈CE, d∈DG, d∈AB).
   If d∈EF: g≠d → two_points_determine_line g d EF DG → EF=DG → d∈EF=DG∩AB → but
   d∈AB and d∈EF=DG — we need a contradiction. Use: EF=DG, d∈AB, d∈DG=EF → DG∩AB exists.
   But DG∥CE and d∈DG∩AB; c∈CE; between c d b → c∈AB → CE∩AB → with DG=EF → EF∥AB but now d∈EF∩AB, contradiction with hEFAB. -/
theorem helper_2_5_step7_dfpar_doff (b c d e : Point) (AB EF : Line)
    (hdAB : d.onLine AB)
    (hcAB : c.onLine AB)
    (heEF : e.onLine EF)
    (hbce : ∠b:c:e = ∟)
    (hcelen : |(c─e)| = |(c─b)|)
    (hcdb : between c d b)
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ¬(d.onLine EF) := by
  intro hdEF
  have hce : c ≠ e := by intro heq; rw [heq] at hcelen; euclid_finish
  have hcb : c ≠ b := (between_symm c d b hcdb).2.2.1
  have heoffAB : ¬(e.onLine AB) := by
    intro heAB
    by_cases hbtw : between b c e
    · euclid_apply (flat_angle_onlyif b c e); euclid_finish
    · euclid_apply (degenerated_angle_if b c e AB); euclid_finish
  have hABneEF : AB ≠ EF := fun heq => heoffAB (heq ▸ heEF)
  exact hEFAB (by euclid_apply (intersection_lines_common_point d EF AB); euclid_finish)

end Elements.Book2
