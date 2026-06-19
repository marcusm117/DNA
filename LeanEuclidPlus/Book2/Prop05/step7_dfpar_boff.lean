import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_boff (b c d e : Point) (AB EF : Line)
    (hbAB : b.onLine AB)
    (hcAB : c.onLine AB)
    (heEF : e.onLine EF)
    (hbce : ∠b:c:e = ∟)
    (hcelen : |(c─e)| = |(c─b)|)
    (hcdb : between c d b)
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ¬(b.onLine EF) := by
  intro hbEF
  have hcb : c ≠ b := (between_symm c d b hcdb).2.2.1
  have hce : c ≠ e := by intro heq; rw [heq] at hcelen; euclid_finish
  have heoffAB : ¬(e.onLine AB) := by
    intro heAB
    by_cases hbtw : between b c e
    · euclid_apply (flat_angle_onlyif b c e); euclid_finish
    · euclid_apply (degenerated_angle_if b c e AB); euclid_finish
  have hABneEF : AB ≠ EF := fun heq => heoffAB (heq ▸ heEF)
  exact hEFAB (by euclid_apply (intersection_lines_common_point b EF AB); euclid_finish)

end Elements.Book2
