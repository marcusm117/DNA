import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.6 sub: DG ∥ BF. DG ∥ CE and CE ∥ BF, so DG ∥ BF [Prop.~1.30]. (Mirror of Prop06 step7_bgdf,
   relabel BG→DG, DF→BF.) Distinctness in-body: DG ≠ CE (d ∈ DG, ¬d ∈ CE), CE ≠ BF (c ∈ CE, ¬c ∈ BF),
   DG ≠ BF (d ∈ DG, ¬d ∈ BF). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_dgbf (b c d : Point) (DG CE BF AB : Line)
    (hdDG : d.onLine DG) (hcCE : c.onLine CE) (hbBF : b.onLine BF) (hcAB : c.onLine AB) (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hdoffCE : ¬(d.onLine CE)) (hcdb : between c d b)
    (hDGCE : ¬(DG.intersectsLine CE)) (hCEBF : ¬(CE.intersectsLine BF)) :
    ¬(DG.intersectsLine BF) := by
  euclid_intros
  have hDGneCE : DG ≠ CE := fun heq => hdoffCE (heq ▸ hdDG)
  have hcoffBF : ¬(c.onLine BF) := by
    intro hcBF
    exact hCEBF (by euclid_apply (intersection_lines_common_point c CE BF); euclid_finish)
  have hCEneBF : CE ≠ BF := fun heq => hcoffBF (heq ▸ hcCE)
  have hdb : d ≠ b := by euclid_finish
  have hdoffBF : ¬(d.onLine BF) := by
    intro hdBF
    euclid_apply (two_points_determine_line d b AB BF)
    euclid_finish
  have hDGneBF : DG ≠ BF := fun heq => hdoffBF (heq ▸ hdDG)
  euclid_apply (proposition_30 DG BF CE)
  euclid_finish

end Elements.Book2
