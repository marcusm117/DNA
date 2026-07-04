import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_13_step8 (a b c d e : Point) (BE : Line)
    (hbetween : between d b c) (hab : a ≠ b)
    (step2 : distinctPointsOnLine b e BE ∧ ∠ c:b:e = ∟)
    (step5 : ∠ c:b:e + ∠ e:b:d = ∠ c:b:a + ∠ a:b:e + ∠ e:b:d)
    (step7 : ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) :
    ∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c := by
  obtain ⟨⟨_, _, hbe⟩, _⟩ := step2
  have hbc : b ≠ c := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have h1 : ∠ c:b:a = ∠ a:b:c := angle_symm c b a ⟨hbc.symm, hab.symm⟩
  have h2 : ∠ a:b:e = ∠ e:b:a := angle_symm a b e ⟨hab, hbe⟩
  have h3 : ∠ e:b:d = ∠ d:b:e := angle_symm e b d ⟨hbe.symm, hbd⟩
  linarith

end Elements.Book1
