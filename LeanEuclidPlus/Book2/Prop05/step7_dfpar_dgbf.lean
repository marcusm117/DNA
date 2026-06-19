import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.7 sub-sub: ¬DG.intersectsLine BF. DG∥CE and CE∥BF → DG∥BF by prop_30.
   Distinctness: DG≠CE (d∈DG, d∉CE derived from hDGCE); CE≠BF (c∈CE, c∉BF);
   DG≠BF (d∈DG, d∉BF via two_points_determine_line from d≠b). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_dgbf (b c d : Point) (AB BF CE DG : Line)
    (hdDG : d.onLine DG) (hcCE : c.onLine CE) (hbBF : b.onLine BF)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hDGCE : ¬(DG.intersectsLine CE))
    (hCEBF : ¬(CE.intersectsLine BF))
    (hcdb : between c d b) :
    ¬(DG.intersectsLine BF) := by
  euclid_intros
  have hdoffCE : ¬(d.onLine CE) := by
    intro hdCE
    exact hDGCE (by euclid_apply (intersection_lines_common_point d DG CE); euclid_finish)
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
