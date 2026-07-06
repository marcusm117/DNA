import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_44_step13_lnek
    (a b e f g h k l : Point) (AB BG EF GF AH KL : Line)
    (hgGF : g.onLine GF) (hhGF : h.onLine GF) (hfGF : f.onLine GF)
    (hkEF : k.onLine EF) (hgEF : g.onLine EF)
    (hhAH : h.onLine AH) (hlAH : l.onLine AH)
    (hfBG : f.onLine BG)
    (hlKL : l.onLine KL) (hkKL : k.onLine KL)
    (hAHEF : ¬AH.intersectsLine EF)
    (hAHBG : ¬AH.intersectsLine BG)
    (step3 : between g f h)
    (hGFAH : GF.intersectsLine AH)
    : l ≠ k := by
  intro heq
  have hkonAH : k.onLine AH := heq ▸ hlAH
  have hAHeqEF : AH = EF := by
    by_contra hne
    exact hAHEF (intersection_lines_common_point k AH EF ⟨hkonAH, hkEF, hne⟩)
  have hgnh : g ≠ h := (between_symm g f h step3).2.2.1
  have hgAH : g.onLine AH := hAHeqEF ▸ hgEF
  have hdp : distinctPointsOnLine g h GF := ⟨hgGF, hhGF, hgnh⟩
  have hGFeqAH : GF = AH := two_points_determine_line g h GF AH ⟨hdp, hgAH, hhAH⟩
  have hGFeqBG : GF = BG := by
    by_contra hne
    exact (hGFeqAH.symm ▸ hAHBG) (intersection_lines_common_point f GF BG ⟨hfGF, hfBG, hne⟩)
  have hAHAH : AH.intersectsLine AH := hGFeqAH ▸ hGFAH
  have hBGeqAH : BG = AH := hGFeqBG.symm.trans hGFeqAH
  exact absurd hAHAH (hBGeqAH ▸ hAHBG)

end Elements.Book1
