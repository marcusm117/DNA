import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.7 sub-sub: the six off-line / non-intersection facts step7_dhg needs but that are
   NOT present at the Main call site (so they cannot be helper hypotheses — derived here in-body
   from the square (hbce, hcelen) + the figure's incidences/parallels, exactly as step7_bmf does).
   Chain: e∉AB (square apex) → b∉EF → d∉CE → e∉DG, b∉DG; h∉AB, h∉EF → KM∥EF (prop_30);
   d,b∉KM (KM∥AB), g∉KM (KM∥EF). -/
theorem helper_2_5_step7_dhg_offs (b c d e g h : Point) (AB BE CE DG EF KM : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (heEF : e.onLine EF) (hgEF : g.onLine EF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG) (hgDG : g.onLine DG)
    (hhKM : h.onLine KM)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hEFAB : ¬(EF.intersectsLine AB))
    (hDGCE : ¬(DG.intersectsLine CE))
    (hbce : ∠ b:c:e = ∟) (hcelen : |(c─e)| = |(c─b)|)
    (hcdb : between c d b) :
    (¬(e.onLine DG)) ∧ (¬(b.onLine DG)) ∧ (¬(KM.intersectsLine EF)) ∧
      (¬(d.onLine KM)) ∧ (¬(b.onLine KM)) ∧ (¬(g.onLine KM)) := by
  euclid_intros
  have heoffAB : ¬(e.onLine AB) := by intro heAB; euclid_finish
  have hboffEF : ¬(b.onLine EF) := by
    intro hbEF
    have hEFneAB : EF ≠ AB := fun heq => heoffAB (heq ▸ heEF)
    euclid_apply (intersection_lines_common_point b EF AB)
    euclid_finish
  have hdoffCE : ¬(d.onLine CE) := by
    intro hdCE
    have hcd : c ≠ d := by euclid_finish
    euclid_apply (two_points_determine_line c d CE AB)
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
  have hhoffAB : ¬(h.onLine AB) := by
    intro hhAB
    have hBEneAB : BE ≠ AB := fun heq => heoffAB (heq ▸ heBE)
    have hhb : h ≠ b := fun heq => hboffDG (heq ▸ hhDG)
    euclid_apply (two_points_determine_line h b BE AB)
    euclid_finish
  have hhoffEF : ¬(h.onLine EF) := by
    intro hhEF
    have hBEneEF : BE ≠ EF := fun heq => hboffEF (heq ▸ hbBE)
    have hhe : h ≠ e := fun heq => heoffDG (heq ▸ hhDG)
    euclid_apply (two_points_determine_line h e EF BE)
    euclid_finish
  have hKMEF : ¬(KM.intersectsLine EF) := by
    have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
    have hEFneAB : EF ≠ AB := fun heq => heoffAB (heq ▸ heEF)
    have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
    euclid_apply (proposition_30 KM EF AB)
    euclid_finish
  have hdoffKM : ¬(d.onLine KM) := by
    intro hdKM
    have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
    euclid_apply (intersection_lines_common_point d KM AB)
    euclid_finish
  have hboffKM : ¬(b.onLine KM) := by
    intro hbKM
    have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
    euclid_apply (intersection_lines_common_point b KM AB)
    euclid_finish
  have hgoffKM : ¬(g.onLine KM) := by
    intro hgKM
    have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
    euclid_apply (intersection_lines_common_point g KM EF)
    euclid_finish
  exact ⟨heoffDG, hboffDG, hKMEF, hdoffKM, hboffKM, hgoffKM⟩

end Elements.Book2
