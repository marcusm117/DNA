import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step7
    (a b d₁ d₂ d₃ e f g h : Point) (AB BG EF GF AH : Line)
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
    (hfeb_angle : ∠ e:b:f = ∠ d₁:d₂:d₃)
    (hd_pos : (∠ d₁:d₂:d₃ : ℝ) > 0)
    (step6 : ∠ a:h:g + ∠ h:g:e = ∟ + ∟)
    : ∠ b:h:f + ∠ f:g:e < ∟ + ∟ := by
  euclid_finish

end Elements.Book1
