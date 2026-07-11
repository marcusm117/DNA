import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step9_ctr_on_AC
    (DEF : Circle) (b h k c₀ : Point) (BH AC : Line)
    (hbDEF : b.onCircle DEF) (hhDEF : h.onCircle DEF)
    (hbBH : b.onLine BH) (hhBH : h.onLine BH)
    (hkBH : k.onLine BH)
    (hc₀offBH : ¬c₀.onLine BH) (hc₀AC : c₀.onLine AC)
    (hkAC : k.onLine AC) (hbkh : between b k h)
    (hbkh' : |(b─k)| = |(k─h)|) (hperp_bkc₀ : ∠ b:k:c₀ = ∟)
    : ∃ o : Point, o.isCentre DEF ∧ o.onLine AC := by
  obtain ⟨o, ho⟩ := exists_centre DEF
  refine ⟨o, ho, ?_⟩
  have h_ob_oh : |(o─b)| = |(o─h)| := by
    have := point_on_circle_onlyif o b h DEF ⟨ho, hbDEF, hhDEF⟩
    linarith
  by_cases hoLBH : o.onLine BH
  · have hok : o = k := by euclid_finish
    rw [hok]; exact hkAC
  · have h_eq_angles : ∠ b:k:o = ∠ o:k:h := by euclid_finish
    have h_bko_perp : ∠ b:k:o = ∟ :=
      perpendicular_if b h k o BH ⟨hbBH, hhBH, hbkh, hoLBH, h_eq_angles⟩
    have hkNo : k ≠ o := fun h => hoLBH (h ▸ hkBH)
    obtain ⟨KO, hkKO, hoKO⟩ := line_from_points k o hkNo
    by_contra h_o_notAC
    have hKONeAC : KO ≠ AC := fun h => h_o_notAC (h ▸ hoKO)
    euclid_finish

end Elements.Book3
