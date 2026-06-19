import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- d.sameSide b EF ∧ ¬(AB.intersectsLine EF) ∧ g ≠ f.
   Uses full figure to derive off-line facts enabling sameSide. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_rest (b c d e f g : Point) (AB BF CE DG EF : Line)
    (hdDG : d.onLine DG) (hgDG : g.onLine DG)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hcCE : c.onLine CE)
    (hgEF : g.onLine EF) (hfEF : f.onLine EF) (heEF : e.onLine EF)
    (hEFAB : ¬(EF.intersectsLine AB))
    (hDGCE : ¬(DG.intersectsLine CE))
    (hCEBF : ¬(CE.intersectsLine BF))
    (hDGBF : ¬(DG.intersectsLine BF))
    (hcdb : between c d b) :
    d.sameSide b EF ∧ ¬(AB.intersectsLine EF) ∧ g ≠ f := by
  euclid_intros
  have hdb : d ≠ b := by euclid_finish
  have hboffDG : ¬(b.onLine DG) := by
    intro hbDG
    euclid_apply (two_points_determine_line b d AB DG)
    euclid_finish
  have hgd : g ≠ d := by euclid_finish
  have hdoffEF : ¬(d.onLine EF) := by
    intro hdEF
    euclid_apply (two_points_determine_line g d EF DG)
    euclid_finish
  have hEFneAB : EF ≠ AB := fun heq => hdoffEF (heq ▸ hdAB)
  have hfb : f ≠ b := by euclid_finish
  have hboffEF : ¬(b.onLine EF) := by
    intro hbEF
    euclid_apply (two_points_determine_line f b EF BF)
    euclid_finish
  have hgoffBF : ¬(g.onLine BF) := by intro hgBF; euclid_finish
  have hgf : g ≠ f := fun heq => hgoffBF (heq ▸ hfBF)
  have hss : d.sameSide b EF := by
    by_contra hns
    euclid_apply (intersection_lines_opposing d b EF AB)
    euclid_finish
  have habef : ¬(AB.intersectsLine EF) := by
    intro hx; euclid_apply (intersection_symm AB EF); euclid_finish
  exact ⟨hss, habef, hgf⟩

end Elements.Book2
