import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step5
    (a b e f g h : Point) (AB BG EF GF AH HB : Line)
    (hhHB : h.onLine HB)
    (hbHB : b.onLine HB)
    (hbet : between a b e)
    (hfGF : f.onLine GF) (hfBG : f.onLine BG)
    (hgGF : g.onLine GF) (hgEF : g.onLine EF)
    (hhGF : h.onLine GF) (hhAH : h.onLine AH)
    (haAH : a.onLine AH) (haAB : a.onLine AB)
    (hbAB : b.onLine AB) (hbBG : b.onLine BG)
    (heAB : e.onLine AB) (heEF : e.onLine EF)
    (hside : f.sameSide b EF)
    (hge : g ≠ e)
    (hab : a ≠ b)
    (hGFAB : ¬GF.intersectsLine AB)
    (hBGEF : ¬BG.intersectsLine EF)
    (hAHBG : ¬AH.intersectsLine BG)
    : distinctPointsOnLine h b HB := by
  have hAHneBG : AH ≠ BG := by euclid_finish
  have hbnotAH : ¬b.onLine AH := fun hbAH =>
    hAHBG (intersection_lines_common_point b AH BG ⟨hbAH, hbBG, hAHneBG⟩)
  exact ⟨hhHB, hbHB, fun heq => hbnotAH (heq ▸ hhAH)⟩

end Elements.Book1
