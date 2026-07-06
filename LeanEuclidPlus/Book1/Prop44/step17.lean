import SystemE
import Book.Prop43
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step17
    (a b e f g h k l m : Point) (AB BG EF GF AH HB KL : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (heAB : e.onLine AB)
    (hfGF : f.onLine GF) (hgGF : g.onLine GF)
    (hbBG : b.onLine BG) (hfBG : f.onLine BG)
    (heEF : e.onLine EF) (hgEF : g.onLine EF)
    (haAH : a.onLine AH) (hhAH : h.onLine AH)
    (hlAH : l.onLine AH) (hlKL : l.onLine KL)
    (hmBG : m.onLine BG) (hmKL : m.onLine KL)
    (hkEF : k.onLine EF) (hkKL : k.onLine KL)
    (hhGF : h.onLine GF) (hhHB : h.onLine HB)
    (hbHB : b.onLine HB) (hkHB : k.onLine HB)
    (hAHEF : ¬AH.intersectsLine EF)
    (hGFAB : ¬GF.intersectsLine AB)
    (hAHBG : ¬AH.intersectsLine BG)
    (hBGEF : ¬BG.intersectsLine EF)
    (hKLAB : ¬KL.intersectsLine AB)
    (step12 : between h a l ∧ between f b m)
    (step13 : formParallelogram h l g k AH EF GF KL)
    (step14 : b.onLine HB ∧ between h b k)
    (step15 : formParallelogram h a f b AH BG GF AB ∧ formParallelogram b m e k BG EF AB KL)
    : Triangle.area △ a:b:m + Triangle.area △ a:l:m =
      Triangle.area △ f:g:e + Triangle.area △ f:e:b := by
  euclid_apply (proposition_43 h g k l f m e a b AH EF GF KL HB BG AB)
  euclid_finish

end Elements.Book1
