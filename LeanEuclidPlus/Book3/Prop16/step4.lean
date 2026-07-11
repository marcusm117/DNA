import SystemE
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_step4
    (d a c b e : Point) (AE : Line)
    (hcne : c ≠ a)
    (right_6 : a ≠ e)
    (left_3 : between a d b)
    (right_4 : ∠ e:a:b = ∟)
    (left_5 : a.onLine AE)
    (left_6 : e.onLine AE)
    (hcAE : c.onLine AE)
    : ∠ d:a:c = ∟ := by
  have hsym := between_symm a d b left_3
  have hab : a ≠ b := hsym.2.2.1
  have had : a ≠ d := hsym.2.1
  obtain ⟨AB, hABa, hABb⟩ := line_from_points a b hab
  have hABd : d.onLine AB := between_same_line_in a d b AB ⟨left_3, hABa, hABb⟩
  -- d is not on AE (if it were, b would be too, making ∠e:a:b degenerate)
  have hd_off : ¬d.onLine AE := by
    intro hd_on
    have hb_on : b.onLine AE := between_same_line_out a d b AE ⟨left_3, left_5, hd_on⟩
    euclid_finish
  -- ∠d:a:e = ∟ (same angle as ∠b:a:e = ∟, with d and b on same ray from a)
  have hdae : ∠ d:a:e = ∟ := by
    euclid_apply (equal_angles a b d e e AB AE)
    euclid_apply (angle_symm b a e)
    euclid_finish
  -- ∠d:a:c = ∟: c is on AE, either same side as e or opposite side from a
  by_cases hcase : between e a c
  · have hflat : ∠ e:a:c = ∟ + ∟ := flat_angle_onlyif e a c hcase
    euclid_finish
  · euclid_apply (equal_angles a d d e c AB AE)
    -- h : ∠d:a:e = ∠d:a:c, hdae : ∠d:a:e = ∟
    exact h.symm.trans hdae

end Elements.Book3
