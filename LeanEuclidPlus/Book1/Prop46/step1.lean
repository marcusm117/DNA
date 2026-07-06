import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step1 (a b c : Point) (AB : Line)
    (h_angle : ∠ b:a:c = ∟)
    (ha_on : a.onLine AB) (hc_off : ¬c.onLine AB)
    (hne : a ≠ b) : ∠ c:a:b = ∟ := by
  have hac : a ≠ c := fun h => hc_off (h ▸ ha_on)
  have hsymm : ∠ b:a:c = ∠ c:a:b := angle_symm b a c ⟨hne.symm, hac⟩
  linarith

end Elements.Book1
