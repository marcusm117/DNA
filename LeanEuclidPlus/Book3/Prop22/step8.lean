import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_22_step8 (a b c d : Point) (AC : Line)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
  (hbAC : ¬b.onLine AC) (hdAC : ¬d.onLine AC)
  (hstep7 : ∠ a:b:c + ∠ b:a:c + ∠ a:c:b = ∠ a:b:c + ∠ a:d:c)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟)   -- "$ABC$, $BAC$, and $ACB$ are equal to two right-angles"
  : ∠ a:b:c + ∠ c:d:a = ∟ + ∟ := by
  have h1 : ∠ b:a:c = ∠ c:a:b := by euclid_finish
  have h2 : ∠ a:c:b = ∠ b:c:a := by euclid_finish
  have h3 : ∠ a:d:c = ∠ c:d:a := by euclid_finish
  linarith [hstep7, hassump1, h1, h2, h3]

end Elements.Book3
