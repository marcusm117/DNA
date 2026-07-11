import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step4
    (ABC : Circle) (b h k c₀ : Point) (BH AC : Line)
    (hbABC : b.onCircle ABC) (hhABC : h.onCircle ABC)
    (hbBH : b.onLine BH) (hhBH : h.onLine BH)
    (hc₀offBH : ¬c₀.onLine BH) (hc₀AC : c₀.onLine AC)
    (hassump1 : k.onLine AC ∧ between b k h ∧ |(b─k)| = |(k─h)| ∧ ∠ b:k:c₀ = ∟)
    : ∃ o : Point, o.isCentre ABC ∧ o.onLine AC := by
  obtain ⟨hkAC, hbkh, hbisect, hperp⟩ := hassump1
  obtain ⟨o, ho⟩ := exists_centre ABC
  refine ⟨o, ho, ?_⟩
  have h_ob_oh : |(o─b)| = |(o─h)| := by
    have := point_on_circle_onlyif o b h ABC ⟨ho, hbABC, hhABC⟩
    linarith
  have hkBH : k.onLine BH := between_same_line_in b k h BH ⟨hbkh, hbBH, hhBH⟩
  by_cases hoLBH : o.onLine BH
  · -- o on BH and equidistant from b,h → o = k (unique midpoint on line)
    have hok : o = k := by euclid_finish
    rw [hok]; exact hkAC
  · -- o off BH → isoceles gives ∠ b:k:o = ∟
    have h_eq_angles : ∠ b:k:o = ∠ o:k:h := by euclid_finish
    have h_bko_perp : ∠ b:k:o = ∟ :=
      perpendicular_if b h k o BH ⟨hbBH, hhBH, hbkh, hoLBH, h_eq_angles⟩
    -- Build auxiliary line KO through k and o
    have hkNo : k ≠ o := fun h => hoLBH (h ▸ hkBH)
    obtain ⟨KO, hkKO, hoKO⟩ := line_from_points k o hkNo
    -- o not on AC → KO ≠ AC
    by_contra h_o_notAC
    have hKONeAC : KO ≠ AC := fun h => h_o_notAC (h ▸ hoKO)
    -- Two distinct lines KO and AC both pass through k and both ⊥ BH at k → False
    euclid_finish

end Elements.Book3
