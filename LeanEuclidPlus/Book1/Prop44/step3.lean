import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step3
    (a b e f g h : Point) (AB BG EF GF AH : Line)
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
    : between g f h := by
  have haeBG : ¬(a.sameSide e BG) := by
    euclid_apply (pasch_3 a b e BG)
    euclid_finish
  have hfnotEF : ¬f.onLine EF := same_side_not_on_line f b EF hside
  have hEFneBG : EF ≠ BG := fun heq => hfnotEF (heq ▸ hfBG)
  have hBGEFsymm : ¬EF.intersectsLine BG := fun h => hBGEF (intersection_symm EF BG h)
  have hsgeBG : g.sameSide e BG := sameSide_of_parallel_both g e EF BG hgEF heEF hEFneBG hBGEFsymm
  have hAHneBG : AH ≠ BG := by euclid_finish
  have hsahBG : h.sameSide a BG := sameSide_of_parallel_both h a AH BG hhAH haAH hAHneBG hAHBG
  euclid_apply (pasch_4 g f h BG GF)
  euclid_finish

end Elements.Book1
