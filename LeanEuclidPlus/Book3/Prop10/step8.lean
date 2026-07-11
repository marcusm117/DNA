import SystemE
import Book1.Prop17.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step8
    (ABC : Circle) (b g h k l c₀ m₀ p : Point)
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
    (step4 : ∃ o : Point, o.isCentre ABC ∧ o.onLine AC)
    (step5 : ∃ o : Point, o.isCentre ABC ∧ o.onLine NO)
    (hpAC : p.onLine AC) (hpNO : p.onLine NO)
    : p.isCentre ABC := by
  obtain ⟨o, ho, hoAC⟩ := step4
  obtain ⟨o', ho', ho'NO⟩ := step5
  have hoo' : o = o' := centre_unique o o' ABC ⟨ho, ho'⟩
  have hoNO : o.onLine NO := hoo' ▸ ho'NO
  have hkBH : k.onLine BH := between_same_line_in b k h BH ⟨hbkh, hbBH, hhBH⟩
  have hlBG : l.onLine BG := between_same_line_in b l g BG ⟨hblg, hbBG, hgBG⟩
  by_cases hop : o = p
  · exact hop ▸ ho
  · exfalso
    have hACNO : AC = NO := two_points_determine_line o p AC NO
      ⟨⟨hoAC, hpAC, hop⟩, hoNO, hpNO⟩
    have hlAC : l.onLine AC := hACNO ▸ hlNO
    have hm₀AC : m₀.onLine AC := hACNO ▸ hm₀NO
    by_cases hkl : k = l
    · -- midpoints coincide: h and g equidistant from k in same direction → h = g
      have hbkg : between b k g := hkl.symm ▸ hblg
      have hkgeq : |(k─g)| = |(k─h)| := by linarith [hkl.symm ▸ hblg']
      euclid_finish
    · -- k ≠ l on AC; form triangle b-k-l with sides BH-AC-BG; both angles at k and l are ∟
      have hbk : b ≠ k := by euclid_finish
      have hbl : b ≠ l := by euclid_finish
      have hboffAC : ¬b.onLine AC := by
        intro hbAC
        exact hc₀offBH ((two_points_determine_line b k BH AC ⟨⟨hbBH, hkBH, hbk⟩, hbAC, hkAC⟩).symm ▸ hc₀AC)
      have hBHneAC : BH ≠ AC := fun h => hc₀offBH (h.symm ▸ hc₀AC)
      have hACneBG : AC ≠ BG := fun h => hm₀offBG (h.symm ▸ hm₀AC)
      have hBHneBG : BH ≠ BG := by
        intro hBHBG
        have hklBG : k.onLine BG := hBHBG ▸ hkBH
        exact hACneBG (two_points_determine_line k l BG AC ⟨⟨hklBG, hlBG, hkl⟩, hkAC, hlAC⟩).symm
      have hTriangle : formTriangle b k l BH AC BG :=
        ⟨⟨hbBH, hkBH, hbk⟩, hkAC, hlAC, hlBG, hbBG, hBHneAC, hACneBG, hBHneBG.symm⟩
      have hangle_sum := Elements.Book1.proposition_17 b k l BH AC BG hTriangle
      -- both interior angles at k and l are right angles
      have hbkl : ∠ b:k:l = ∟ := by euclid_finish
      have hklb : ∠ k:l:b = ∟ := by euclid_finish
      linarith

end Elements.Book3
