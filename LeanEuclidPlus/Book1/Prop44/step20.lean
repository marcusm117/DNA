import SystemE
import Book1.Prop15.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step20
    (a b e f h l m d₁ d₂ d₃ : Point) (AB AH BG EF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (heAB : e.onLine AB)
    (hbBG : b.onLine BG) (hfBG : f.onLine BG) (hmBG : m.onLine BG)
    (heEF : e.onLine EF)
    (hside : f.sameSide b EF)
    (hBGEF : ¬BG.intersectsLine EF)
    (step2 : between a b e)
    (step12 : between h a l ∧ between f b m)
    (hassump1 : ∠ e:b:f = ∠ a:b:m)
    (hassump2 : ∠ e:b:f = ∠ d₁:d₂:d₃)
    : ∠ a:b:m = ∠ d₁:d₂:d₃ := by
  have hfbm : between f b m := step12.2
  euclid_apply (proposition_15 e a m f b AB BG)
  euclid_finish

end Elements.Book1
