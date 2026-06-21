import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.15 sub: between l h m (l = CE ∩ KM, h = BG ∩ KM, m = DF ∩ KM, all on KM). l (on CE, left of BG)
   and m (on DF, right of BG) are on opposite sides of the middle vertical BG: l ~ c (both on CE ∥ BG,
   step7_sscl), c ≁ d (step7_cnsdBG), d ~ m (both on DF ∥ BG), so l ≁ m. pasch_4 on l, h, m across BG
   and KM gives between l h m. -/
theorem helper_2_6_step15_lhm (b c d h l m : Point) (CE DF BG KM : Line)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (hmDF : m.onLine DF) (hdDF : d.onLine DF)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM) (hmKM : m.onLine KM)
    (hboffCE : ¬(b.onLine CE)) (hboffDF : ¬(b.onLine DF))
    (hsscl : c.sameSide l BG) (hcnsd : ¬(c.sameSide d BG))
    (hBGCE : ¬(BG.intersectsLine CE)) (hBGDF : ¬(BG.intersectsLine DF)) :
    between l h m := by
  euclid_intros
  have hBGneCE : BG ≠ CE := fun heq => hboffCE (heq ▸ hbBG)
  have hBGneDF : BG ≠ DF := fun heq => hboffDF (heq ▸ hbBG)
  have hloffBG : ¬(l.onLine BG) := by
    intro hon; euclid_apply (intersection_lines_common_point l BG CE); euclid_finish
  have hmoffBG : ¬(m.onLine BG) := by
    intro hon; euclid_apply (intersection_lines_common_point m BG DF); euclid_finish
  have hdoffBG : ¬(d.onLine BG) := by
    intro hon; euclid_apply (intersection_lines_common_point d BG DF); euclid_finish
  have hdssm : d.sameSide m BG := by
    by_contra hns; euclid_apply (intersection_lines_opposing d m BG DF); euclid_finish
  have hlnsm : ¬(l.sameSide m BG) := by euclid_finish
  have hlh : l ≠ h := fun heq => hloffBG (heq ▸ hhBG)
  have hmh : m ≠ h := fun heq => hmoffBG (heq ▸ hhBG)
  euclid_apply (pasch_4 l h m BG KM)
  euclid_finish

end Elements.Book2
