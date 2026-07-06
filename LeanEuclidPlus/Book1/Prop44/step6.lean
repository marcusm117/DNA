import SystemE
import Book1.Prop29.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step6
    (a b e f g h : Point) (AB BG EF GF AH HB : Line)
    (hfGF : f.onLine GF) (hfBG : f.onLine BG)
    (hgGF : g.onLine GF) (hgEF : g.onLine EF)
    (hhGF : h.onLine GF) (hhAH : h.onLine AH)
    (haAH : a.onLine AH) (haAB : a.onLine AB)
    (hbBG : b.onLine BG) (hbAB : b.onLine AB)
    (heEF : e.onLine EF) (heAB : e.onLine AB)
    (hside : f.sameSide b EF)
    (hge : g ≠ e)
    (hab : a ≠ b)
    (step3 : between g f h)
    (hGFAB : ¬GF.intersectsLine AB)
    (hBGEF : ¬BG.intersectsLine EF)
    (hAHBG : ¬AH.intersectsLine BG)
    (hassump1 : ¬(AH.intersectsLine EF) ∧ GF.intersectsLine AH ∧ GF.intersectsLine EF)
    : ∠ a:h:g + ∠ h:g:e = ∟ + ∟ := by
  euclid_apply (proposition_29''''' e a g h EF AH GF)
  euclid_finish

end Elements.Book1
