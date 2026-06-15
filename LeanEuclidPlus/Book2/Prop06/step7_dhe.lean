import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: between d h e. h = BG ∩ DE; d, e are the ends of the diagonal DE, on opposite sides of
   the middle vertical BG (step7_dnseBG: ¬d.sameSide e BG). pasch_4 on d, h, e across BG and DE gives
   between d h e. Distinctness: BG ≠ DE (b ∈ BG, ¬b ∈ DE); d ≠ e (d ∈ AB, ¬e ∈ AB); d ≠ h (d ∈ DF,
   ¬h ∈ DF); e ≠ h (h ∈ BG, ¬e ∈ BG). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step7_dhe (b d e h : Point) (AB DF BG DE : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (hhBG : h.onLine BG) (hbBG : b.onLine BG)
    (hdAB : d.onLine AB) (hdDF : d.onLine DF)
    (hboffDE : ¬(b.onLine DE)) (heoffAB : ¬(e.onLine AB))
    (hhoffDF : ¬(h.onLine DF)) (heoffBG : ¬(e.onLine BG))
    (hdnseBG : ¬(d.sameSide e BG)) :
    between d h e := by
  euclid_intros
  have hBGneDE : BG ≠ DE := fun heq => hboffDE (heq ▸ hbBG)
  have hde : d ≠ e := fun heq => heoffAB (heq ▸ hdAB)
  have hdh : d ≠ h := fun heq => hhoffDF (heq ▸ hdDF)
  have heh : e ≠ h := fun heq => heoffBG (heq ▸ hhBG)
  euclid_apply (pasch_4 d h e BG DE)
  euclid_finish

end Elements.Book2
