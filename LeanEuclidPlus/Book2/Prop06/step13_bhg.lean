import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.13 sub: between b h g. h = KM ∩ BG; b (on AB, above KM) and g (on EF, below KM) are the two
   ends of the middle vertical BG inside the square, so the crossing h lies between them. b and g are
   on opposite sides of KM: b ~ d (both on AB ∥ KM, step7_ssdb), d ≁ e (step7_dnse), e ~ g (both on
   EF ∥ KM), so b ≁ g. pasch_4 on b, h, g across KM and BG gives between b h g. -/
theorem helper_2_6_step13_bhg (b d e g h : Point) (AB EF BG KM : Line)
    (hbAB : b.onLine AB) (hgEF : g.onLine EF) (heEF : e.onLine EF)
    (hbBG : b.onLine BG) (hgBG : g.onLine BG) (hhBG : h.onLine BG)
    (hhKM : h.onLine KM)
    (hhoffAB : ¬(h.onLine AB)) (hhoffEF : ¬(h.onLine EF))
    (hssdb : d.sameSide b KM) (hdnse : ¬(d.sameSide e KM))
    (hKMAB : ¬(KM.intersectsLine AB)) (hKMEF : ¬(KM.intersectsLine EF)) :
    between b h g := by
  euclid_intros
  have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
  have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
  have hboffKM : ¬(b.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point b KM AB); euclid_finish
  have hKMneBG : KM ≠ BG := fun heq => hboffKM (heq ▸ hbBG)
  have hgoffKM : ¬(g.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point g KM EF); euclid_finish
  have heoffKM : ¬(e.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point e KM EF); euclid_finish
  have hssg : e.sameSide g KM := by
    by_contra hns; euclid_apply (intersection_lines_opposing e g KM EF); euclid_finish
  have hbnsg : ¬(b.sameSide g KM) := by euclid_finish
  have hbh : b ≠ h := fun heq => hhoffAB (heq ▸ hbAB)
  have hgh : g ≠ h := fun heq => hhoffEF (heq ▸ hgEF)
  euclid_apply (pasch_4 b h g KM BG)
  euclid_finish

end Elements.Book2
