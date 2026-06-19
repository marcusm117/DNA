import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.7 sub: formParallelogram c b l m AB KM CE BF (rectangle CM).
   hboffKM (b∉KM) and hcsslBF (c.sameSide l BF) are absent from the call site; derived in-body.
   Chain: e∉AB (square) → d∉CE → b∉DG → h∉AB → KM≠AB → b∉KM → b≠m.
   CE≠BF (e∉BF from sameSide) → c,l∉BF → c.sameSide l BF. -/
theorem helper_2_5_step7_cmpar (b c d e h l m : Point) (AB KM CE BF BE DG : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hlKM : l.onLine KM) (hmKM : m.onLine KM) (hhKM : h.onLine KM)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE) (heCE : e.onLine CE)
    (hbBF : b.onLine BF) (hmBF : m.onLine BF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hCEBF : ¬(CE.intersectsLine BF))
    (hDGCE : ¬(DG.intersectsLine CE))
    (hecBF : e.sameSide c BF)
    (hcelen : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟)
    (hcdb : between c d b) :
    formParallelogram c b l m AB KM CE BF := by
  euclid_intros
  have heoffAB : ¬(e.onLine AB) := by intro heAB; euclid_finish
  have heoffBF : ¬(e.onLine BF) := by euclid_finish
  have hCEneBF : CE ≠ BF := fun heq => heoffBF (heq ▸ heCE)
  have hcoffBF : ¬(c.onLine BF) := by
    by_contra hcBF
    euclid_apply (intersection_lines_common_point c CE BF)
    euclid_finish
  have hloffBF : ¬(l.onLine BF) := by
    by_contra hlBF
    euclid_apply (intersection_lines_common_point l CE BF)
    euclid_finish
  have hcsslBF : c.sameSide l BF := by
    by_contra hns
    euclid_apply (intersection_lines_opposing c l BF CE)
    euclid_finish
  have hdoffCE : ¬(d.onLine CE) := by
    intro hdCE
    have hcd : c ≠ d := by euclid_finish
    euclid_apply (two_points_determine_line c d CE AB)
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
  have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
  have hboffKM : ¬(b.onLine KM) := by
    intro hbKM
    euclid_apply (intersection_lines_common_point b KM AB)
    euclid_finish
  have hbm : b ≠ m := fun heq => hboffKM (heq ▸ hmKM)
  have hABKM : ¬(AB.intersectsLine KM) := by
    intro hx; euclid_apply (intersection_symm AB KM); euclid_finish
  exact ⟨hcAB, hbAB, hlKM, hmKM, hcCE, hlCE, ⟨hbBF, hmBF, hbm⟩, hcsslBF, hABKM, hCEBF⟩

end Elements.Book2
