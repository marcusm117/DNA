import SystemE
import Book1.Prop17.Main
import Mathlib.Tactic.Linarith
import Book3.Prop10.step9_ctr_on_AC
import Book3.Prop10.step9_ctr_on_NO
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step9
    (DEF : Circle) (b g h k l c₀ m₀ p : Point)
    (BH BG AC NO : Line)
    (hbBH : b.onLine BH) (hhBH : h.onLine BH)
    (hbBG : b.onLine BG) (hgBG : g.onLine BG)
    (hkAC : k.onLine AC) (hc₀AC : c₀.onLine AC)
    (hlNO : l.onLine NO) (hm₀NO : m₀.onLine NO)
    (hc₀offBH : ¬c₀.onLine BH)
    (hm₀offBG : ¬m₀.onLine BG)
    (hperp_bkc₀ : ∠ b:k:c₀ = ∟)
    (hperp_blm₀ : ∠ b:l:m₀ = ∟)
    (hbkh : between b k h) (hbkh' : |(b─k)| = |(k─h)|)
    (hblg : between b l g) (hblg' : |(b─l)| = |(l─g)|)
    (hbh : b ≠ h) (hbg : b ≠ g) (hgh : g ≠ h)
    (hbDEF : b.onCircle DEF) (hgDEF : g.onCircle DEF) (hhDEF : h.onCircle DEF)
    (hpAC : p.onLine AC) (hpNO : p.onLine NO)
    : p.isCentre DEF := by
  have hkBH : k.onLine BH := between_same_line_in b k h BH ⟨hbkh, hbBH, hhBH⟩
  have hlBG : l.onLine BG := between_same_line_in b l g BG ⟨hblg, hbBG, hgBG⟩
  -- center of DEF lies on the perp-bisector of BH (= AC)
  have step9_ctr_on_AC : ∃ o : Point, o.isCentre DEF ∧ o.onLine AC := by euclid_apply (helper_3_10_step9_ctr_on_AC DEF b h k c₀ BH AC (by euclid_assumption "" (show b.onCircle DEF; assumption)) (by euclid_assumption "" (show h.onCircle DEF; assumption)) (by euclid_assumption "" (show b.onLine BH; assumption)) (by euclid_assumption "" (show h.onLine BH; assumption)) (by euclid_assumption "" (show k.onLine BH; assumption)) (by euclid_assumption "" (show ¬c₀.onLine BH; assumption)) (by euclid_assumption "" (show c₀.onLine AC; assumption)) (by euclid_assumption "" (show k.onLine AC; assumption)) (by euclid_assumption "" (show between b k h; assumption)) (by euclid_assumption "" (show |(b─k)| = |(k─h)|; assumption)) (by euclid_assumption "" (show ∠ b:k:c₀ = ∟; assumption)))
  -- center of DEF lies on the perp-bisector of BG (= NO)
  have step9_ctr_on_NO : ∃ o : Point, o.isCentre DEF ∧ o.onLine NO := by euclid_apply (helper_3_10_step9_ctr_on_NO DEF b g l m₀ BG NO (by euclid_assumption "" (show b.onCircle DEF; assumption)) (by euclid_assumption "" (show g.onCircle DEF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show l.onLine BG; assumption)) (by euclid_assumption "" (show ¬m₀.onLine BG; assumption)) (by euclid_assumption "" (show m₀.onLine NO; assumption)) (by euclid_assumption "" (show l.onLine NO; assumption)) (by euclid_assumption "" (show between b l g; assumption)) (by euclid_assumption "" (show |(b─l)| = |(l─g)|; assumption)) (by euclid_assumption "" (show ∠ b:l:m₀ = ∟; assumption)))
  -- conclude p = center of DEF (same argument as step8)
  obtain ⟨o, ho, hoAC⟩ := step9_ctr_on_AC
  obtain ⟨o', ho', ho'NO⟩ := step9_ctr_on_NO
  have hoo' : o = o' := centre_unique o o' DEF ⟨ho, ho'⟩
  have hoNO : o.onLine NO := hoo' ▸ ho'NO
  by_cases hop : o = p
  · exact hop ▸ ho
  · exfalso
    have hACNO : AC = NO := two_points_determine_line o p AC NO
      ⟨⟨hoAC, hpAC, hop⟩, hoNO, hpNO⟩
    have hlAC : l.onLine AC := hACNO ▸ hlNO
    have hm₀AC : m₀.onLine AC := hACNO ▸ hm₀NO
    by_cases hkl : k = l
    · have hbkg : between b k g := hkl.symm ▸ hblg
      have hkgeq : |(k─g)| = |(k─h)| := by linarith [hkl.symm ▸ hblg']
      euclid_finish
    · have hbk : b ≠ k := by euclid_finish
      have hbl : b ≠ l := by euclid_finish
      have hBHneAC : BH ≠ AC := fun h => hc₀offBH (h.symm ▸ hc₀AC)
      have hACneBG : AC ≠ BG := fun h => hm₀offBG (h.symm ▸ hm₀AC)
      have hBHneBG : BH ≠ BG := by
        intro hBHBG
        have hklBG : k.onLine BG := hBHBG ▸ hkBH
        exact hACneBG (two_points_determine_line k l BG AC ⟨⟨hklBG, hlBG, hkl⟩, hkAC, hlAC⟩).symm
      have hTriangle : formTriangle b k l BH AC BG :=
        ⟨⟨hbBH, hkBH, hbk⟩, hkAC, hlAC, hlBG, hbBG, hBHneAC, hACneBG, hBHneBG.symm⟩
      have hangle_sum := Elements.Book1.proposition_17 b k l BH AC BG hTriangle
      have hbkl : ∠ b:k:l = ∟ := by euclid_finish
      have hklb : ∠ k:l:b = ∟ := by euclid_finish
      linarith

end Elements.Book3
