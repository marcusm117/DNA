import SystemE
import Book.Prop30
import Book1.Prop44.step12_hal
import Book1.Prop44.step12_fbm
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step12
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
    (hlAH : l.onLine AH) (hlKL : l.onLine KL)
    (hmBG : m.onLine BG) (hmKL : m.onLine KL)
    : between h a l ∧ between f b m := by
  have hKLGF : ¬KL.intersectsLine GF := by
    euclid_apply (proposition_30 KL GF AB)
    euclid_finish
  have step12_hal : between h a l := by euclid_apply (helper_1_44_step12_hal a b e f g h k l m AB BG EF GF AH HB KL (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show between a b e; assumption)) (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show f.onLine BG; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show f.sameSide b EF; assumption)) (by euclid_assumption "" (show g ≠ e; assumption)) (by euclid_assumption "" (show ¬GF.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬BG.intersectsLine EF; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine EF; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine GF; assumption)) (by euclid_assumption "" (show h.onLine HB; assumption)) (by euclid_assumption "" (show b.onLine HB; assumption)) (by euclid_assumption "" (show k.onLine HB; assumption)) (by euclid_assumption "" (show k.onLine EF; assumption)) (by euclid_assumption "" (show k.onLine KL; assumption)) (by euclid_assumption "" (show ¬KL.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬KL.intersectsLine GF; assumption)) (by euclid_assumption "" (show l.onLine AH; assumption)) (by euclid_assumption "" (show l.onLine KL; assumption)) (by euclid_assumption "" (show m.onLine BG; assumption)) (by euclid_assumption "" (show m.onLine KL; assumption)))
  have step12_fbm : between f b m := by euclid_apply (helper_1_44_step12_fbm a b e f g h k l m AB BG EF GF AH HB KL (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show between a b e; assumption)) (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show f.onLine BG; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show f.sameSide b EF; assumption)) (by euclid_assumption "" (show g ≠ e; assumption)) (by euclid_assumption "" (show ¬GF.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬BG.intersectsLine EF; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine EF; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine GF; assumption)) (by euclid_assumption "" (show h.onLine HB; assumption)) (by euclid_assumption "" (show b.onLine HB; assumption)) (by euclid_assumption "" (show k.onLine HB; assumption)) (by euclid_assumption "" (show k.onLine EF; assumption)) (by euclid_assumption "" (show k.onLine KL; assumption)) (by euclid_assumption "" (show ¬KL.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬KL.intersectsLine GF; assumption)) (by euclid_assumption "" (show l.onLine AH; assumption)) (by euclid_assumption "" (show l.onLine KL; assumption)) (by euclid_assumption "" (show m.onLine BG; assumption)) (by euclid_assumption "" (show m.onLine KL; assumption)))
  exact ⟨step12_hal, step12_fbm⟩

end Elements.Book1
