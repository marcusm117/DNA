import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.7 sub: between b m f (m = KM ∩ BF lies between b and f on BF).
   b and f are on opposite sides of KM; m = KM ∩ BF; pasch_4 gives between b m f.
   The four absent-from-call-site hyps (heoffDG, hboffDG, hhoffEF, hKMEF) are
   derived in-body from the square (hcelen, hbce) + incidence/parallel hypotheses. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_bmf (b c d e f h m : Point) (AB BF BE EF CE DG KM : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hmBF : m.onLine BF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hhKM : h.onLine KM) (hmKM : m.onLine KM)
    (hcelen : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟)
    (hKMAB : ¬(KM.intersectsLine AB)) (hEFAB : ¬(EF.intersectsLine AB))
    (hCEBF : ¬(CE.intersectsLine BF)) (hDGCE : ¬(DG.intersectsLine CE))
    (hecBF : e.sameSide c BF) (hcdb : between c d b) :
    between b m f := by
  euclid_intros
  have heoffAB : ¬(e.onLine AB) := by
    intro heAB
    euclid_finish
  have hdoffCE : ¬(d.onLine CE) := by
    intro hdCE
    have hcd : c ≠ d := by euclid_finish
    euclid_apply (two_points_determine_line c d CE AB)
    euclid_finish
  have hboffEF : ¬(b.onLine EF) := by
    intro hbEF
    have hEFneAB : EF ≠ AB := fun heq => heoffAB (heq ▸ heEF)
    euclid_apply (intersection_lines_common_point b EF AB)
    euclid_finish
  have heoffDG : ¬(e.onLine DG) := by
    intro heDG
    have hDGneCE : DG ≠ CE := fun heq => hdoffCE (heq ▸ hdDG)
    euclid_apply (intersection_lines_common_point e DG CE)
    euclid_finish
  have hboffDG : ¬(b.onLine DG) := by
    intro hbDG
    have hbd : b ≠ d := by euclid_finish
    euclid_apply (two_points_determine_line b d AB DG)
    euclid_finish
  have hhoffEF : ¬(h.onLine EF) := by
    intro hhEF
    have hBEneEF : BE ≠ EF := fun heq => hboffEF (heq ▸ hbBE)
    have hhe : h ≠ e := fun heq => heoffDG (heq ▸ hhDG)
    euclid_apply (two_points_determine_line h e EF BE)
    euclid_finish
  have hhoffAB : ¬(h.onLine AB) := by
    intro hhAB
    have hBEneAB : BE ≠ AB := fun heq => heoffAB (heq ▸ heBE)
    have hhb : h ≠ b := fun heq => hboffDG (heq ▸ hhDG)
    euclid_apply (two_points_determine_line h b BE AB)
    euclid_finish
  have hKMEF : ¬(KM.intersectsLine EF) := by
    euclid_intros
    have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
    have hEFneAB : EF ≠ AB := fun heq => heoffAB (heq ▸ heEF)
    have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
    euclid_apply (proposition_30 KM EF AB)
    euclid_finish
  have step7_bmf_opp : ¬(b.sameSide f KM) := by euclid_finish
  euclid_apply (pasch_4 b m f KM BF)
  euclid_finish

end Elements.Book2
