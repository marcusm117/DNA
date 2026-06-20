import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.15 sub: between e g f (e = CE ∩ EF, g = BG ∩ EF, f = DF ∩ EF, all on EF). e (on CE, left of BG)
   and f (on DF, right of BG) are on opposite sides of the middle vertical BG: e ~ c (both on CE ∥ BG,
   step7_sscebg), c ≁ d (step7_cnsdBG), d ~ f (both on DF ∥ BG), so e ≁ f. pasch_4 on e, g, f across BG
   and EF gives between e g f. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step15_egf (b c d e f g : Point) (CE DF BG EF : Line)
    (heCE : e.onLine CE) (hcCE : c.onLine CE)
    (hfDF : f.onLine DF) (hdDF : d.onLine DF)
    (hbBG : b.onLine BG) (hgBG : g.onLine BG)
    (heEF : e.onLine EF) (hgEF : g.onLine EF) (hfEF : f.onLine EF)
    (hboffCE : ¬(b.onLine CE)) (hboffDF : ¬(b.onLine DF))
    (hsscebg : c.sameSide e BG) (hcnsd : ¬(c.sameSide d BG))
    (hBGCE : ¬(BG.intersectsLine CE)) (hBGDF : ¬(BG.intersectsLine DF)) :
    between e g f := by
  euclid_intros
  have hBGneCE : BG ≠ CE := fun heq => hboffCE (heq ▸ hbBG)
  have hBGneDF : BG ≠ DF := fun heq => hboffDF (heq ▸ hbBG)
  have heoffBG : ¬(e.onLine BG) := by
    intro hon; euclid_apply (intersection_lines_common_point e BG CE); euclid_finish
  have hfoffBG : ¬(f.onLine BG) := by
    intro hon; euclid_apply (intersection_lines_common_point f BG DF); euclid_finish
  have hdoffBG : ¬(d.onLine BG) := by
    intro hon; euclid_apply (intersection_lines_common_point d BG DF); euclid_finish
  have hdssf : d.sameSide f BG := by
    by_contra hns; euclid_apply (intersection_lines_opposing d f BG DF); euclid_finish
  have hensf : ¬(e.sameSide f BG) := by euclid_finish
  have heg : e ≠ g := fun heq => heoffBG (heq ▸ hgBG)
  have hfg : f ≠ g := fun heq => hfoffBG (heq ▸ hgBG)
  euclid_apply (pasch_4 e g f BG EF)
  euclid_finish

end Elements.Book2
