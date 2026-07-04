import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_13_step12 (a b c d : Point)
    (hbetween : between d b c) (hab : a ≠ b)
    (step10 : ∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c)
    (step11 : ∠ c:b:e + ∠ e:b:d = ∟ + ∟) :
    ∠ c:b:a + ∠ a:b:d = ∟ + ∟ := by
  have hbc : b ≠ c := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have h1 : ∠ a:b:c = ∠ c:b:a := angle_symm a b c ⟨hab, hbc⟩
  have h2 : ∠ d:b:a = ∠ a:b:d := angle_symm d b a ⟨hbd.symm, hab.symm⟩
  linarith

end Elements.Book1
