import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step6_assumption1
    (a b e f g h : Point) (AB BG EF GF AH : Line)
    (hhGF : h.onLine GF) (hhAH : h.onLine AH)
    (hgGF : g.onLine GF) (hgEF : g.onLine EF)
    (hfGF : f.onLine GF) (hfBG : f.onLine BG)
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
    : ¬(AH.intersectsLine EF) ∧ GF.intersectsLine AH ∧ GF.intersectsLine EF := by
  have hAHEF : ¬AH.intersectsLine EF := by
    euclid_apply (proposition_30 AH EF BG)
    euclid_finish
  have hGFneAH : GF ≠ AH := by euclid_finish
  have hGFAH : GF.intersectsLine AH :=
    intersection_lines_common_point h GF AH ⟨hhGF, hhAH, hGFneAH⟩
  have hGFneEF : GF ≠ EF := by euclid_finish
  have hGFEF : GF.intersectsLine EF :=
    intersection_lines_common_point g GF EF ⟨hgGF, hgEF, hGFneEF⟩
  exact ⟨hAHEF, hGFAH, hGFEF⟩

end Elements.Book1
