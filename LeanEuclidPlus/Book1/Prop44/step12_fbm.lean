import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step12_fbm
    (a b e f g h k l m : Point) (AB BG EF GF AH HB KL : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (heAB : e.onLine AB)
    (hab : a ≠ b)
    (hbet : between a b e)
    (hfGF : f.onLine GF) (hgGF : g.onLine GF)
    (hbBG : b.onLine BG) (hfBG : f.onLine BG)
    (heEF : e.onLine EF) (hgEF : g.onLine EF)
    (hside : f.sameSide b EF)
    (hge : g ≠ e)
    (hGFAB : ¬GF.intersectsLine AB)
    (hBGEF : ¬BG.intersectsLine EF)
    (haAH : a.onLine AH)
    (hAHBG : ¬AH.intersectsLine BG)
    (hAHEF : ¬AH.intersectsLine EF)
    (hhAH : h.onLine AH) (hhGF : h.onLine GF)
    (hhHB : h.onLine HB) (hbHB : b.onLine HB)
    (hkHB : k.onLine HB) (hkEF : k.onLine EF)
    (hkKL : k.onLine KL) (hKLAB : ¬KL.intersectsLine AB)
    (hKLGF : ¬KL.intersectsLine GF)
    (hlAH : l.onLine AH) (hlKL : l.onLine KL)
    (hmBG : m.onLine BG) (hmKL : m.onLine KL)
    : between f b m := by
  euclid_assert ¬(f.onLine AB)
  euclid_assert ¬(m.onLine AB)
  euclid_assert ¬(f.sameSide m AB)
  euclid_apply (pasch_4 f b m AB BG)
  euclid_finish

end Elements.Book1
